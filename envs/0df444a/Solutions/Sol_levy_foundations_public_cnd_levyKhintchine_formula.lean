-- Prove2me | solution 1 for levy_foundations_public_cnd_levyKhintchine_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:01:36.457496+00:00
-- url     : https://prove2.me/submissions/9fe69830-7076-4219-9095-c0c2981bebce

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_psi_decomposition_of_semigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

/-- The CND exponent generates a convolution semigroup, whose triplet
decomposition yields the original Lévy–Khintchine integral formula. -/
theorem solution
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : ProbabilityTheory.IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ∃ T : ProbabilityTheory.LevyKhintchineTriple, ∀ ξ : ℝ,
      ψ ξ = ↑T.drift * ↑ξ * Complex.I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + MeasureTheory.integral T.levyMeasure
            (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) := by
  let S := ProbabilityTheory.convolutionSemigroupOfCND
    hψ_cont hψ_zero hψ_cnd hψ_herm
  obtain ⟨b, σ, ν, hν, hEq⟩ :=
    levy_foundations_public_psi_decomposition_of_semigroup S
  refine ⟨⟨b, σ, ν, hν⟩, ?_⟩
  intro ξ
  exact hEq ξ
