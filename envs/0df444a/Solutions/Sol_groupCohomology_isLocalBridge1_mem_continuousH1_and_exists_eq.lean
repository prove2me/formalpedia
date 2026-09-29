-- Prove2me | solution 1 for groupCohomology.isLocalBridge1_mem_continuousH1_and_exists_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ae837ec2-fa7d-5224-9ebd-3832553f82a6

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

def homAdd {V W : Rep.{0} k D} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom

lemma homAdd_apply {V W : Rep.{0} k D} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

def homOfLinear {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) : V ⟶ W :=
  Rep.ofHom ⟨L, fun d => LinearMap.ext (hL d)⟩

lemma homOfLinear_hom_apply {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) (v : V) :
    (homOfLinear L hL).hom v = L v := rfl

def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) : P →+ A := ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h)

lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π ψ h x = A.ρ h (ev π ψ (P.ρ (π h⁻¹) x)) - ev π ψ x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ h ψ - ψ) x = _
  rw [ev_sub]
  congr 1

lemma cob_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ + ψ') h x = cob π ψ h x + cob π ψ' h x := by
  simp only [cob, map_add, Pi.add_apply, ev_add]

lemma cob_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ - ψ') h x = cob π ψ h x - cob π ψ' h x := by
  simp only [cob, map_sub, Pi.sub_apply, ev_sub]

lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma ρ_one_apply {V : Rep.{0} k D} (v : V) : V.ρ 1 v = v := by
  rw [map_one, Module.End.one_apply]

lemma ρ_inv_ρ {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d⁻¹ (V.ρ d v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hκ in

lemma κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hfg hg hκ in

lemma exists_forall_κ_eq (c : P →+ A) (hc : ∀ x : R, c (f.hom x) = 0) : ∃ m : M, ∀ x : P, κ (g.hom x) m = c x := by
  classical

  have hker : ∀ y y' : P, g.hom y = g.hom y' → c y = c y' := by
    intro y y' hyy'
    have h0 : g.hom (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    obtain ⟨x, hx⟩ := (hfg _).1 h0
    have := hc x
    rw [hx, map_sub, sub_eq_zero] at this
    exact this
  let s : B → P := Function.surjInv hg
  have hs : ∀ b, g.hom (s b) = b := Function.surjInv_eq hg
  let cB : B →+ A :=
    { toFun := fun b => c (s b)
      map_zero' := by rw [hker (s 0) 0 (by rw [hs, map_zero]), map_zero]
      map_add' := fun b b' => by rw [← map_add, hker (s (b + b')) (s b + s b') (by rw [hs, map_add, hs, hs])] }
  obtain ⟨m, hm, -⟩ := hκ cB
  exact ⟨m, fun x => by rw [hm]; exact hker _ _ (hs _)⟩

include hιeq in

lemma cob_apply_f (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : R) : cob π ψ h (f.hom x) = 0 := by
  rw [cob_apply, ← Rep.hom_comm_apply f, hψ, hψ, Rep.hom_comm_apply φ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma κ_ρ (h : H) (b : B) (m : M) : κ b (M.ρ h m) = A.ρ h (κ (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ρ_ρ_inv]

noncomputable def nOf (ψ : (ihom (Rep.res π P)).obj A) (h : H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x then hex.choose else 0

include hfg hg hκ hιeq in
lemma κ_nOf (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) (cob_apply_f π f ι hιeq φ ψ hψ h)
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₁_of_forall_κ (ψ : (ihom (Rep.res π P)).obj A) (n : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : n ∈ cocycles₁ M := by
  rw [mem_cocycles₁_iff]
  intro h₁ h₂
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [map_add, hn, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hn, hn]
  simp only [cob_apply, map_mul, mul_inv_rev, Module.End.mul_apply, map_sub]
  abel

include hg hκ hκeq in

lemma sub_mem_coboundaries₁ (ψ ψ' : (ihom (Rep.res π P)).obj A) (n n' : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) (hn' : ∀ (h : H) (x : P), κ (g.hom x) (n' h) = cob π ψ' h x)
    (m₀ : M) (hm₀ : ∀ x : P, κ (g.hom x) m₀ = ev π (ψ - ψ') x) : n - n' ∈ coboundaries₁ M := by
  refine ⟨m₀, funext fun h => ?_⟩
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [d₀₁_hom_apply, Pi.sub_apply, map_sub, map_sub, hn, hn', κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm₀, hm₀, ← cob_sub,
    cob_apply]

include hιeq in

lemma cob_eq_zero_of_hom (χ : P ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : P, ev π ψ x = ι (χ.hom x)) (h : H) (x : P) :
    cob π ψ h x = 0 := by
  rw [cob_apply, hψ, hψ, Rep.hom_comm_apply χ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma cob_of_κ (m₀ : M) (θ : (ihom (Rep.res π P)).obj A) (hθ : ∀ x : P, ev π θ x = κ (g.hom x) m₀) (h : H) (x : P) :
    cob π θ h x = κ (g.hom x) (M.ρ h m₀) - κ (g.hom x) m₀ := by
  rw [cob_apply, hθ, hθ, Rep.hom_comm_apply g, ← κ_ρ π κ hκeq]

lemma ρ_ev_of_cob_eq_zero (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (h : H) (x : P) :
    A.ρ h (ev π ψ x) = ev π ψ (P.ρ (π h) x) := by
  have := hψ h (P.ρ (π h) x)
  rw [cob_apply, sub_eq_zero, map_inv, ρ_inv_ρ] at this
  exact this

lemma ρ_ev_of_cob_eq_zero_of_ker (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (s : H)
    (hs : π s = 1) (x : P) : A.ρ s (ev π ψ x) = ev π ψ x := by
  rw [ρ_ev_of_cob_eq_zero π ψ hψ, hs, map_one, Module.End.one_apply]

lemma ev_ext {s t : (ihom (Rep.res π P)).obj A} (hst : ∀ x : P, ev π s x = ev π t x) : s = t := LinearMap.ext hst

lemma ev_ρ (h : H) (t : (ihom (Rep.res π P)).obj A) (x : P) :
    ev π (((ihom (Rep.res π P)).obj A).ρ h t) x = A.ρ h (ev π t (P.ρ (π h⁻¹) x)) := rfl

include hg hκ in

lemma isLevelConstant₁_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (ψ : (ihom (Rep.res π P)).obj A)
    (hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (ev π ψ x) = ev π ψ x)
    (n : H → M) (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : IsLevelConstant₁ r n := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hψlev
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun h s hs => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hn, hn, cob_apply, cob_apply, mul_inv_rev, map_mul π, map_inv π s, hs₁, inv_one, one_mul, map_mul, Module.End.mul_apply,
    hs₂]

end hyps

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

end LB1EX

open LB1EX in
theorem solution
    {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {D : Type} [Group D] (π : H →* D) (hπ : Function.Surjective π)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    (hιfix : ∀ a : A, (∀ s : H, π s = 1 → A.ρ s a = a) → ∃ x : X, ι x = a)
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R ⟶ X, ∃ ψ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x)
    (h90 : ∀ u : cocycles₁ ((ihom (Rep.res π P)).obj A), IsLevelConstant₁ r (u : H → (ihom (Rep.res π P)).obj A) →
      ∃ χ : (ihom (Rep.res π P)).obj A,
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ = (u : H → (ihom (Rep.res π P)).obj A))
    {Λ : (R ⟶ X) →+ H1 M} (hΛ : IsLocalBridge₁ π f g ι κ Λ) :
    (∀ φ : R ⟶ X, Λ φ ∈ continuousH1 r M) ∧ (∀ y ∈ continuousH1 r M, ∃ φ : R ⟶ X, Λ φ = y) := by
  classical
  have _ := hι
  constructor
  ·
    intro φ
    obtain ⟨ψ, hψ, hψlev⟩ := hdiv φ
    have hψ' : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x) := hψ
    have hn := κ_nOf π f g ι κ hfg hg hιeq hκ φ ψ hψ'
    have hcoc := mem_cocycles₁_of_forall_κ π g κ hg hκeq hκ ψ _ hn
    rw [hΛ φ ψ hψ _ hn hcoc]
    exact H1π_mem_continuousH1 r M (isLevelConstant₁_of_forall_κ π g κ hg hκ r hπlev ψ hψlev _ hn)
  ·
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_continuousH1_iff r M y).1 hy

    let θ : M → (ihom (Rep.res π P)).obj A := fun m => toIntLinearMapOfModules _ _ ((κ.flip m).comp (homAdd g))
    have hθ : ∀ (m : M) (x : P), ev π (θ m) x = κ (g.hom x) m := fun m x => rfl
    have hu : (θ ∘ c : H → (ihom (Rep.res π P)).obj A) ∈ cocycles₁ ((ihom (Rep.res π P)).obj A) := by
      rw [mem_cocycles₁_iff]
      intro h₁ h₂
      apply ev_ext π
      intro x
      rw [ev_add, ev_ρ]
      simp only [Function.comp_apply, hθ]
      rw [(mem_cocycles₁_iff (c : H → M)).1 c.2, map_add, κ_ρ π κ hκeq, Rep.hom_comm_apply g]
    have hulev : IsLevelConstant₁ r (θ ∘ c : H → (ihom (Rep.res π P)).obj A) := hc.comp θ
    obtain ⟨χ₀, hχ₀lev, hdχ₀⟩ := h90 ⟨_, hu⟩ hulev
    have hcob : ∀ (h : H) (x : P), cob π χ₀ h x = κ (g.hom x) (c h) := by
      intro h x
      have := congrFun hdχ₀ h
      change (d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ₀ h = θ (c h) at this
      change ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ₀ h) x = _
      rw [this, hθ]

    have hgf : ∀ x : R, g.hom (f.hom x) = 0 := fun x => (hfg (f.hom x)).2 ⟨x, rfl⟩
    have hfix : ∀ (h : H) (x : R), A.ρ h (ev π χ₀ (f.hom x)) = ev π χ₀ (P.ρ (π h) (f.hom x)) := by
      intro h x
      have := hcob h (P.ρ (π h) (f.hom x))
      rw [cob_apply, map_inv, ρ_inv_ρ, Rep.hom_comm_apply g, hgf, map_zero, map_zero, AddMonoidHom.zero_apply, sub_eq_zero] at this
      exact this
    choose φf hφf using fun x : R =>
      hιfix (ev π χ₀ (f.hom x)) (fun s hs => by rw [hfix, hs, ρ_one_apply])
    have φf_add : ∀ x y, φf (x + y) = φf x + φf y := fun x y => hι (by
      rw [map_add, hφf, hφf, hφf, ← homAdd_apply f, ← homAdd_apply f, ← homAdd_apply f, map_add (homAdd f), map_add (ev π χ₀)])
    have φf_ρ : ∀ (d : D) (x : R), φf (R.ρ d x) = X.ρ d (φf x) := by
      intro d x
      obtain ⟨h, rfl⟩ := hπ d
      apply hι
      rw [hφf, hιeq, hφf, hfix, Rep.hom_comm_apply f]
    let φ : R ⟶ X := homOfLinear (toIntLinearMapOfModules _ _ (AddMonoidHom.mk' φf φf_add)) (fun d x => φf_ρ d x)
    refine ⟨φ, ?_⟩
    have hψ : ∀ x : R, LinearMap.toAddMonoidHom χ₀ (f.hom x) = ι (φ.hom x) := fun x => (hφf x).symm
    have hn : ∀ (h : H) (x : P), κ (g.hom x) ((c : H → M) h) = LinearMap.toAddMonoidHom ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ₀ h) x :=
      fun h x => (hcob h x).symm
    rw [hΛ φ χ₀ hψ (c : H → M) hn c.2]
    rfl

end S_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq
end P2MW
export P2MW.S_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq (solution)
