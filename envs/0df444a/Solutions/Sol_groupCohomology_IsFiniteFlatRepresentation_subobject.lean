-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatRepresentation.subobject
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:45.279012+00:00
-- url     : https://prove2.me/submissions/568f9340-0dab-47db-aad4-79eb364dd006

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- An equivariant additive injection realizes the source as a stable subobject
of a finite-flat local action. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hU : IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u))
    (i : W →+ U) (hi : Function.Injective i)
    (hiact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      i (σ • w) = σ • i w) :
    IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w) := by
  classical
  let T : W ≃+ i.range := AddMonoidHom.ofInjective hi
  have hstable : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (u : U),
      u ∈ i.range → σ • u ∈ i.range := by
    intro σ u hu
    obtain ⟨w, rfl⟩ := hu
    exact ⟨σ • w, hiact σ w⟩
  apply hU.subquotient p i.range hstable T.symm.toAddMonoidHom T.symm.surjective
  intro σ u
  apply hi
  change i ((AddMonoidHom.ofInjective hi).symm ⟨σ • (u : U), hstable σ u u.2⟩) =
    i (σ • (AddMonoidHom.ofInjective hi).symm u)
  rw [AddMonoidHom.apply_ofInjective_symm, hiact,
    AddMonoidHom.apply_ofInjective_symm]

end groupCohomology
