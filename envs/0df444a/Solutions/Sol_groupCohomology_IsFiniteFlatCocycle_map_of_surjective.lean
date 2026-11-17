-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatCocycle.map_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:44.58031+00:00
-- url     : https://prove2.me/submissions/5f8d2127-44a6-4b7f-ba82-c1751b81717c

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_quotient
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- A quotient of coefficient representations takes an admissible cocycle to an
admissible cocycle by the induced surjection on its cocycle extension. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (q : W →ₗ[ZMod p] U) (hq : Function.Surjective q)
    (hqact : ∀ σ w, q (ρ σ w) = τ σ (q w))
    (hqc : ∀ σ, q (c σ) = d σ)
    (hc : IsFiniteFlatCocycle p ρ c) : IsFiniteFlatCocycle p τ d := by
  letI := cocycleExtensionAction p ρ c
  letI := cocycleExtensionAction p τ d
  let Q : (W × ZMod p) →+ (U × ZMod p) :=
    { toFun := fun x => (q x.1, x.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp }
  apply IsFiniteFlatRepresentation.quotient p hc Q
  · intro u
    obtain ⟨w, hw⟩ := hq u.1
    exact ⟨(w, u.2), Prod.ext hw rfl⟩
  · intro σ x
    apply Prod.ext
    · change q (ρ σ x.1 + x.2 • c σ) = τ σ (q x.1) + x.2 • d σ
      rw [map_add, map_smul, hqact, hqc]
    · rfl

end groupCohomology
