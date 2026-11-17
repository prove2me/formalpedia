-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatRepresentation.quotient
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:43.953014+00:00
-- url     : https://prove2.me/submissions/6d3d75bc-85bd-4d3f-9fe1-1b5ddab23780

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- A surjective equivariant additive map transports finite-flat local models. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hW : IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w))
    (q : W →+ U) (hq : Function.Surjective q)
    (hqact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      q (σ • w) = σ • q w) :
    IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u) := by
  let qt : (⊤ : AddSubgroup W) →+ U :=
    { toFun := fun w => q w
      map_zero' := q.map_zero
      map_add' := fun x y => q.map_add x y }
  apply hW.subquotient p ⊤ (fun _ _ _ => trivial) qt
  · intro u
    obtain ⟨w, hw⟩ := hq u
    exact ⟨⟨w, trivial⟩, hw⟩
  · intro σ w
    exact hqact σ w

end groupCohomology
