-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatRepresentation.subquotient
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:43.25763+00:00
-- url     : https://prove2.me/submissions/5ac3c74c-dd5f-42ad-a0b4-b82f686e43c4

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- Finite-flat local actions pass to equivariant additive quotients of stable subgroups. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hW : IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w))
    (P : AddSubgroup W)
    (hP : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      w ∈ P → σ • w ∈ P)
    (q : P →+ U) (hq : Function.Surjective q)
    (hqact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : P),
      q ⟨σ • (w : W), hP σ w w.2⟩ = σ • q w) :
    IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u) := by
  rcases hW with ⟨H, hH, hHopf, hfin, hflat, hcomm, e, he, hact⟩
  letI := hH
  letI := hHopf
  letI := hfin
  letI := hflat
  letI := hcomm
  exact HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_subquotient
    p H e he hact P hP q hq hqact

end groupCohomology
