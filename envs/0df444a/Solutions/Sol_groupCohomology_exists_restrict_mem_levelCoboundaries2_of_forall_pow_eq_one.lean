-- Prove2me | solution 1 for groupCohomology.exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/48744e56-f245-5383-b35e-86f2a8eca9ab

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology

theorem solution
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup G) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (C : Set (Subgroup G)) (hC : ∀ S ∈ C, ∀ N : ℕ, 0 < N → S ⊓ T N ∈ C)
    (base : ∀ S ∈ C, ∀ a : S × S → Rep.trivial (ZMod p) S (ZMod p),
      a ∈ levelCocycles₂ (r.comp S.subtype) (Rep.trivial (ZMod p) S (ZMod p)) →
        ∃ (N : ℕ) (_ : 0 < N),
          (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
              a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
            ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
                (Rep.trivial (ZMod p) ↥(S ⊓ T N) (ZMod p)))
    (S : Subgroup G) (hS : S ∈ C) (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hP : ∀ s : S, ∃ n : ℕ, B.ρ (s ^ p ^ n) = 1)
    (b : S × S → B) (hb : b ∈ levelCocycles₂ (r.comp S.subtype) B) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
          b (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
            (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)) B) := by
  classical

  have resCocy : ∀ (S S' : Subgroup G) (h : S' ≤ S) (B : Rep.{0} (ZMod p) S) (x : S × S → B),
      x ∈ levelCocycles₂ (r.comp S.subtype) B →
      (fun g : S' × S' => x (Subgroup.inclusion h g.1, Subgroup.inclusion h g.2))
        ∈ levelCocycles₂ ((r.comp S.subtype).comp (Subgroup.inclusion h)) (Rep.res (Subgroup.inclusion h) B) :=
    fun S S' h B x hx =>
      cochainsPullPush₂_mem_levelCocycles₂ (rH := r.comp S.subtype) (rG := (r.comp S.subtype).comp (Subgroup.inclusion h))
        (A := B) (B := Rep.res (Subgroup.inclusion h) B) (Subgroup.inclusion h) (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hx
  have resCob : ∀ (S S' : Subgroup G) (h : S' ≤ S) (B : Rep.{0} (ZMod p) S) (x : S × S → B),
      x ∈ levelCoboundaries₂ (r.comp S.subtype) B →
      (fun g : S' × S' => x (Subgroup.inclusion h g.1, Subgroup.inclusion h g.2))
        ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion h)) (Rep.res (Subgroup.inclusion h) B) :=
    fun S S' h B x hx =>
      cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r.comp S.subtype) (rG := (r.comp S.subtype).comp (Subgroup.inclusion h))
        (A := B) (B := Rep.res (Subgroup.inclusion h) B) (Subgroup.inclusion h) (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hx

  have fixvec : ∀ (S : Subgroup G) (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B],
      (∀ s : S, ∃ n : ℕ, B.ρ (s ^ p ^ n) = 1) → 0 < Module.finrank (ZMod p) B →
      ∃ v : B, v ≠ 0 ∧ ∀ s : S, B.ρ s v = v := by
    intro S B _ hP hd
    haveI : Finite B := Module.finite_of_finite (ZMod p)
    let Γ : Subgroup (B →ₗ[ZMod p] B)ˣ := B.ρ.asGroupHom.range
    have hΓ : IsPGroup p Γ := by
      rintro ⟨γ, s, rfl⟩
      obtain ⟨n, hn⟩ := hP s
      refine ⟨n, Subtype.ext (Units.ext ?_)⟩
      show (((B.ρ.asGroupHom s) ^ p ^ n : (B →ₗ[ZMod p] B)ˣ) : B →ₗ[ZMod p] B) = 1
      rw [← map_pow, Representation.asGroupHom_apply, hn]
    have hcard : p ∣ Nat.card B := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := B), Nat.card_zmod]
      exact dvd_pow_self p hd.ne'
    have h0 : (0 : B) ∈ MulAction.fixedPoints Γ B := fun γ => smul_zero _
    obtain ⟨v, hv, hv0⟩ := hΓ.exists_fixed_point_of_prime_dvd_card_of_fixed_point B hcard h0
    refine ⟨v, fun h => hv0 h.symm, fun s => ?_⟩
    have := hv ⟨B.ρ.asGroupHom s, s, rfl⟩
    exact this

  suffices key : ∀ (d : ℕ) (S : Subgroup G), S ∈ C → ∀ (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B],
      Module.finrank (ZMod p) B = d →
      (∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b) →
      (∀ s : S, ∃ n : ℕ, B.ρ (s ^ p ^ n) = 1) →
      ∀ b : S × S → B, b ∈ levelCocycles₂ (r.comp S.subtype) B →
        ∃ (N : ℕ) (_ : 0 < N),
          (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
              b (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
            ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
                (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)) B) by
    exact key _ S hS B rfl hsm hP b hb
  intro d
  induction d using Nat.strong_induction_on with | _ d IH =>
  intro S hS B _ hd hsm hP b hb
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  ·
    subst hd0
    haveI : Subsingleton B := Module.finrank_zero_iff.1 hd
    refine ⟨1, one_pos, ?_⟩
    have : (fun g : ↥(S ⊓ T 1) × ↥(S ⊓ T 1) => b (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2)) = 0 :=
      funext fun _ => Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  obtain ⟨v, hv0, hv⟩ := fixvec S B hP (hd ▸ hdpos)
  let W : Submodule (ZMod p) B := (ZMod p) ∙ v
  have hWfix : ∀ (s : S) (w : B), w ∈ W → B.ρ s w = w := by
    intro s w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, hv]
  have hW : ∀ s : S, W ≤ W.comap (B.ρ s) := fun s w hw => by
    show B.ρ s w ∈ W
    rw [hWfix s w hw]; exact hw
  let A : Rep.{0} (ZMod p) S := Rep.of (B.ρ.subrepresentation W hW)
  let Cq : Rep.{0} (ZMod p) S := Rep.quotient B W hW
  let φ : A ⟶ B := Rep.ofHom (W.subtype.intertwiningMap_of_isIntertwiningMap A.ρ B.ρ (fun _ _ => rfl))
  let ψ : B ⟶ Cq := Rep.ofHom (W.mkQ.intertwiningMap_of_isIntertwiningMap B.ρ Cq.ρ (fun _ _ => rfl))
  have hφ : ∀ a : A, φ.hom a = (a : B) := fun _ => rfl
  have hψ : ∀ x : B, ψ.hom x = Submodule.Quotient.mk x := fun _ => rfl
  have hφinj : Function.Injective φ.hom := fun a a' h => Subtype.ext h
  have hψsurj : Function.Surjective ψ.hom := Submodule.Quotient.mk_surjective W
  have hex : ∀ x : B, ψ.hom x = 0 ↔ ∃ a : A, φ.hom a = x := by
    intro x
    rw [hψ, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hAtriv : ∀ (s : S) (a : A), A.ρ s a = a := fun s a => Subtype.ext (hWfix s a a.2)
  have hA1 : Module.finrank (ZMod p) A = 1 := finrank_span_singleton hv0

  have hdC : Module.finrank (ZMod p) Cq = d - 1 := by
    have := Submodule.finrank_quotient_add_finrank W
    rw [finrank_span_singleton hv0, hd] at this
    show Module.finrank (ZMod p) (B ⧸ W) = d - 1
    omega
  have hsmC : ∀ x : Cq, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → Cq.ρ s x = x := by
    intro x
    obtain ⟨y, rfl⟩ := hψsurj x
    obtain ⟨F, hF, h⟩ := hsm y
    exact ⟨F, hF, fun s hs => by rw [← Rep.hom_comm_apply, h s hs]⟩
  have hPC : ∀ s : S, ∃ n : ℕ, Cq.ρ (s ^ p ^ n) = 1 := by
    intro s
    obtain ⟨n, hn⟩ := hP s
    refine ⟨n, LinearMap.ext fun x => ?_⟩
    obtain ⟨y, rfl⟩ := hψsurj x
    rw [← Rep.hom_comm_apply, hn]
    rfl

  have hψb : (ψ.hom ∘ b) ∈ levelCocycles₂ (r.comp S.subtype) Cq :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := r.comp S.subtype) (rG := r.comp S.subtype) (A := B) (B := Cq)
      (MonoidHom.id S) (fun _ => rfl) ψ.hom.toLinearMap (fun g x => Rep.hom_comm_apply ψ g x) hb
  obtain ⟨N₁, hN₁, h₁⟩ := IH (d - 1) (by omega) S hS Cq hdC hsmC hPC (ψ.hom ∘ b) hψb

  have hS₁ : S ⊓ T N₁ ∈ C := hC S hS N₁ hN₁
  let i₁ : ↥(S ⊓ T N₁) →* S := Subgroup.inclusion inf_le_left
  let r₁ := (r.comp S.subtype).comp i₁
  let φ₁ : Rep.res i₁ A ⟶ Rep.res i₁ B :=
    Rep.ofHom (W.subtype.intertwiningMap_of_isIntertwiningMap (Rep.res i₁ A).ρ (Rep.res i₁ B).ρ (fun _ _ => rfl))
  let ψ₁ : Rep.res i₁ B ⟶ Rep.res i₁ Cq :=
    Rep.ofHom (W.mkQ.intertwiningMap_of_isIntertwiningMap (Rep.res i₁ B).ρ (Rep.res i₁ Cq).ρ (fun _ _ => rfl))
  have hsm₁ : ∀ x : Rep.res i₁ B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : ↥(S ⊓ T N₁), r₁ s ∈ F.fixingSubgroup → (Rep.res i₁ B).ρ s x = x := by
    intro x
    obtain ⟨F, hF, h⟩ := hsm x
    exact ⟨F, hF, fun s hs => h (i₁ s) hs⟩
  let b₁ : ↥(S ⊓ T N₁) × ↥(S ⊓ T N₁) → Rep.res i₁ B := fun g => b (i₁ g.1, i₁ g.2)
  have hb₁ : b₁ ∈ levelCocycles₂ r₁ (Rep.res i₁ B) := resCocy S _ inf_le_left B b hb
  have hφ₁inj : Function.Injective φ₁.hom := fun a a' h => Subtype.ext h
  have hψ₁surj : Function.Surjective ψ₁.hom := Submodule.Quotient.mk_surjective W
  have hexr : ∀ x : Rep.res i₁ B, ψ₁.hom x = 0 ↔ ∃ a : Rep.res i₁ A, φ₁.hom a = x := by
    intro x
    show Submodule.Quotient.mk x = 0 ↔ ∃ a : A, (a : B) = x
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hex₁ := groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp r₁
    (A := Rep.res i₁ A) (B := Rep.res i₁ B) (C := Rep.res i₁ Cq) φ₁ ψ₁ hφ₁inj hψ₁surj hexr hsm₁ b₁ hb₁
  have hfun : (ψ₁.hom ∘ b₁) = fun g : ↥(S ⊓ T N₁) × ↥(S ⊓ T N₁) =>
      (ψ.hom ∘ b) (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2) :=
    funext fun _ => rfl
  have h₁' : (ψ₁.hom ∘ b₁) ∈ levelCoboundaries₂ r₁ (Rep.res i₁ Cq) := by
    rw [hfun]; exact h₁
  obtain ⟨a, ha, hba⟩ := hex₁.1 h₁'

  let e : A ≃ₗ[ZMod p] ZMod p := LinearEquiv.ofFinrankEq _ _ (by rw [hA1, Module.finrank_self])
  let a' : ↥(S ⊓ T N₁) × ↥(S ⊓ T N₁) → Rep.trivial (ZMod p) ↥(S ⊓ T N₁) (ZMod p) := fun g => e (a g)
  have ha' : a' ∈ levelCocycles₂ r₁ (Rep.trivial (ZMod p) ↥(S ⊓ T N₁) (ZMod p)) :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := r₁) (rG := r₁) (A := Rep.res i₁ A) (B := Rep.trivial (ZMod p) ↥(S ⊓ T N₁) (ZMod p))
      (MonoidHom.id _) (fun _ => rfl) (e : A →ₗ[ZMod p] ZMod p) (fun s x => by
        show e (A.ρ (i₁ s) x) = e x
        rw [hAtriv]) ha
  obtain ⟨N₂, hN₂, h₂⟩ := base _ hS₁ a' ha'

  let i₂ : ↥((S ⊓ T N₁) ⊓ T N₂) →* ↥(S ⊓ T N₁) := Subgroup.inclusion inf_le_left
  let r₂ := r₁.comp i₂

  have ha₂ : (fun g : ↥((S ⊓ T N₁) ⊓ T N₂) × ↥((S ⊓ T N₁) ⊓ T N₂) => a (i₂ g.1, i₂ g.2))
      ∈ levelCoboundaries₂ r₂ (Rep.res i₂ (Rep.res i₁ A)) := by
    have := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r₂) (rG := r₂)
      (A := Rep.trivial (ZMod p) ↥((S ⊓ T N₁) ⊓ T N₂) (ZMod p)) (B := Rep.res i₂ (Rep.res i₁ A))
      (MonoidHom.id _) (fun _ => rfl) (e.symm : ZMod p →ₗ[ZMod p] A) (fun s x => by
        show e.symm x = A.ρ (i₁ (i₂ s)) (e.symm x)
        rw [hAtriv]) h₂
    convert this using 1
    funext g
    exact (e.symm_apply_apply (a (i₂ g.1, i₂ g.2))).symm

  have hb₂ : (fun g : ↥((S ⊓ T N₁) ⊓ T N₂) × ↥((S ⊓ T N₁) ⊓ T N₂) => b (i₁ (i₂ g.1), i₁ (i₂ g.2)))
      ∈ levelCoboundaries₂ r₂ (Rep.res i₂ (Rep.res i₁ B)) := by
    have hdiff := resCob (S ⊓ T N₁) ((S ⊓ T N₁) ⊓ T N₂) inf_le_left (Rep.res i₁ B) (b₁ - φ₁.hom ∘ a) hba
    have hφa := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r₂) (rG := r₂)
      (A := Rep.res i₂ (Rep.res i₁ A)) (B := Rep.res i₂ (Rep.res i₁ B))
      (MonoidHom.id _) (fun _ => rfl) W.subtype (fun _ _ => rfl) ha₂
    have hsum := Submodule.add_mem _ hdiff hφa
    convert hsum using 1
    all_goals try rfl
    funext g
    show b (i₁ (i₂ g.1), i₁ (i₂ g.2)) = (b (i₁ (i₂ g.1), i₁ (i₂ g.2)) - (a (i₂ g.1, i₂ g.2) : B)) + (a (i₂ g.1, i₂ g.2) : B)
    rw [sub_add_cancel]

  have hle : S ⊓ T (N₁ * N₂) ≤ (S ⊓ T N₁) ⊓ T N₂ :=
    le_inf (le_inf inf_le_left (inf_le_right.trans (hT N₁ (N₁ * N₂) hN₁ (dvd_mul_right _ _))))
      (inf_le_right.trans (hT N₂ (N₁ * N₂) hN₂ (dvd_mul_left _ _)))
  refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, ?_⟩
  exact resCob ((S ⊓ T N₁) ⊓ T N₂) (S ⊓ T (N₁ * N₂)) hle (Rep.res i₂ (Rep.res i₁ B)) _ hb₂

end S_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
end P2MW
export P2MW.S_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one (solution)
