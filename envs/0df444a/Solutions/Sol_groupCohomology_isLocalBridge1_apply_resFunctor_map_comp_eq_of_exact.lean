-- Prove2me | solution 1 for groupCohomology.isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5acfc7d4-1479-5e02-9fb5-7559bc21e872

import Mathlib
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact

set_option autoImplicit false
set_option maxHeartbeats 3200000
open CategoryTheory groupCohomology

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

private def homAdd {V W : Rep.{0} k D} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom

private lemma homAdd_apply {V W : Rep.{0} k D} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

private def homOfLinear {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) : V ⟶ W :=
  Rep.ofHom ⟨L, fun d => LinearMap.ext (hL d)⟩

private lemma homOfLinear_hom_apply {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) (v : V) :
    (homOfLinear L hL).hom v = L v := rfl

private def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

private lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
private lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

private noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) : P →+ A := ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h)

private lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π ψ h x = A.ρ h (ev π ψ (P.ρ (π h⁻¹) x)) - ev π ψ x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ h ψ - ψ) x = _
  rw [ev_sub]
  congr 1

private lemma cob_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ + ψ') h x = cob π ψ h x + cob π ψ' h x := by
  simp only [cob, map_add, Pi.add_apply, ev_add]

private lemma cob_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ - ψ') h x = cob π ψ h x - cob π ψ' h x := by
  simp only [cob, map_sub, Pi.sub_apply, ev_sub]

private lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private lemma ρ_one_apply {V : Rep.{0} k D} (v : V) : V.ρ 1 v = v := by
  rw [map_one, Module.End.one_apply]

private lemma ρ_inv_ρ {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d⁻¹ (V.ρ d v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hκ in

private lemma κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hfg hg hκ in

private lemma exists_forall_κ_eq (c : P →+ A) (hc : ∀ x : R, c (f.hom x) = 0) : ∃ m : M, ∀ x : P, κ (g.hom x) m = c x := by
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

private lemma cob_apply_f (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : R) : cob π ψ h (f.hom x) = 0 := by
  rw [cob_apply, ← Rep.hom_comm_apply f, hψ, hψ, Rep.hom_comm_apply φ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

private lemma κ_ρ (h : H) (b : B) (m : M) : κ b (M.ρ h m) = A.ρ h (κ (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ρ_ρ_inv]

private noncomputable def nOf (ψ : (ihom (Rep.res π P)).obj A) (h : H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x then hex.choose else 0

include hfg hg hκ hιeq in
private lemma κ_nOf (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) (cob_apply_f π f ι hιeq φ ψ hψ h)
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

private lemma mem_cocycles₁_of_forall_κ (ψ : (ihom (Rep.res π P)).obj A) (n : H → M)
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

private lemma sub_mem_coboundaries₁ (ψ ψ' : (ihom (Rep.res π P)).obj A) (n n' : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) (hn' : ∀ (h : H) (x : P), κ (g.hom x) (n' h) = cob π ψ' h x)
    (m₀ : M) (hm₀ : ∀ x : P, κ (g.hom x) m₀ = ev π (ψ - ψ') x) : n - n' ∈ coboundaries₁ M := by
  refine ⟨m₀, funext fun h => ?_⟩
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [d₀₁_hom_apply, Pi.sub_apply, map_sub, map_sub, hn, hn', κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm₀, hm₀, ← cob_sub,
    cob_apply]

include hιeq in

private lemma cob_eq_zero_of_hom (χ : P ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : P, ev π ψ x = ι (χ.hom x)) (h : H) (x : P) :
    cob π ψ h x = 0 := by
  rw [cob_apply, hψ, hψ, Rep.hom_comm_apply χ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

private lemma cob_of_κ (m₀ : M) (θ : (ihom (Rep.res π P)).obj A) (hθ : ∀ x : P, ev π θ x = κ (g.hom x) m₀) (h : H) (x : P) :
    cob π θ h x = κ (g.hom x) (M.ρ h m₀) - κ (g.hom x) m₀ := by
  rw [cob_apply, hθ, hθ, Rep.hom_comm_apply g, ← κ_ρ π κ hκeq]

private lemma ρ_ev_of_cob_eq_zero (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (h : H) (x : P) :
    A.ρ h (ev π ψ x) = ev π ψ (P.ρ (π h) x) := by
  have := hψ h (P.ρ (π h) x)
  rw [cob_apply, sub_eq_zero, map_inv, ρ_inv_ρ] at this
  exact this

private lemma ρ_ev_of_cob_eq_zero_of_ker (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (s : H)
    (hs : π s = 1) (x : P) : A.ρ s (ev π ψ x) = ev π ψ x := by
  rw [ρ_ev_of_cob_eq_zero π ψ hψ, hs, map_one, Module.End.one_apply]

private lemma ev_ext {s t : (ihom (Rep.res π P)).obj A} (hst : ∀ x : P, ev π s x = ev π t x) : s = t := LinearMap.ext hst

private lemma ev_ρ (h : H) (t : (ihom (Rep.res π P)).obj A) (x : P) :
    ev π (((ihom (Rep.res π P)).obj A).ρ h t) x = A.ρ h (ev π t (P.ρ (π h⁻¹) x)) := rfl

include hg hκ in

private lemma isLevelConstant₁_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
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

private def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

private theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

end LB1EX

open LB1EX in
theorem solution
    {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {D D' : Type} [Group D] [Group D'] (π : H →* D) (π' : H →* D') (ψ : D' →* D)
    (hψ : ∀ h : H, ψ (π' h) = π h)

    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B) (hg : Function.Surjective g.hom)
    (hfg : Function.Exact f.hom g.hom)
    {R' P' : Rep ℤ D'} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res ψ B) (hg' : Function.Surjective g'.hom)
    (ρR : R' ⟶ Rep.res ψ R) (ρP : P' ⟶ Rep.res ψ P)
    (hsqf : ρR ≫ (Rep.resFunctor ψ).map f = f' ≫ ρP)
    (hsqg : ρP ≫ (Rep.resFunctor ψ).map g = g')

    {X : Rep ℤ D} {X' : Rep ℤ D'} {A : Rep ℤ H} (ι : X →+ A) (ι' : X' →+ A)
    (jX : Rep.res ψ X ⟶ X') (hj : ∀ x : X, ι' (jX.hom x) = ι x)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))

    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))

    (hdiv : ∀ φ : R ⟶ X, ∃ χ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom χ (f.hom x) = ι (φ.hom x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x)
    {Λ : (R ⟶ X) →+ H1 M} (hΛ : IsLocalBridge₁ π f g ι κ Λ)
    {Λ' : (R' ⟶ X') →+ H1 M} (hΛ' : IsLocalBridge₁ π' f' g' ι' κ Λ') :
    ∀ φ : R ⟶ X, Λ' (ρR ≫ (Rep.resFunctor ψ).map φ ≫ jX) = Λ φ := by
  classical
  have _ := hg'
  intro φ

  obtain ⟨χ, hχ, -⟩ := hdiv φ
  have hχ' : ∀ x : R, ev π χ (f.hom x) = ι (φ.hom x) := hχ
  have hn := κ_nOf π f g ι κ hfg hg hιeq hκ φ χ hχ'
  have hcoc := mem_cocycles₁_of_forall_κ π g κ hg hκeq hκ χ _ hn
  have hΛφ : Λ φ = (H1π M).hom ⟨_, hcoc⟩ := hΛ φ χ hχ _ hn hcoc

  let χ' : (ihom (Rep.res π' P')).obj A := toIntLinearMapOfModules _ _ ((ev π χ).comp (homAdd ρP))
  have hev' : ∀ x' : P', ev π' χ' x' = ev π χ (ρP.hom x') := fun _ => rfl
  have hχ'f : ∀ x' : R', LinearMap.toAddMonoidHom χ' (f'.hom x') = ι' ((ρR ≫ (Rep.resFunctor ψ).map φ ≫ jX).hom x') := by
    intro x'
    have hsq : f.hom (ρR.hom x') = ρP.hom (f'.hom x') := by
      have := congrArg (fun τ => Rep.Hom.hom τ x') hsqf
      simpa [Rep.hom_comp] using this
    change ev π χ (ρP.hom (f'.hom x')) = ι' (jX.hom (φ.hom (ρR.hom x')))
    rw [hj, ← hsq, hχ']
  have hcob' : ∀ (h : H) (x' : P'), cob π' χ' h x' = cob π χ h (ρP.hom x') := by
    intro h x'
    rw [cob_apply, cob_apply, hev', hev', Rep.hom_comm_apply]
    change A.ρ h (ev π χ (P.ρ (ψ (π' h⁻¹)) (ρP.hom x'))) - _ = _
    rw [hψ h⁻¹]
  have hn' : ∀ (h : H) (x' : P'), κ (g'.hom x') (nOf π g κ χ h) = LinearMap.toAddMonoidHom ((d₀₁ ((ihom (Rep.res π' P')).obj A)).hom χ' h) x' := by
    intro h x'
    change κ (g'.hom x') (nOf π g κ χ h) = cob π' χ' h x'
    rw [hcob', ← hn h (ρP.hom x'), ← hsqg]
    rfl
  rw [hΛφ]
  exact hΛ' _ χ' hχ'f _ hn' hcoc

end S_groupCohomology_isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact
end P2MW
export P2MW.S_groupCohomology_isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact (solution)
