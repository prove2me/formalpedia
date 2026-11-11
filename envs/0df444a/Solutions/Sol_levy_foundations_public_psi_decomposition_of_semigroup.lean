-- Prove2me | solution 1 for levy_foundations_public_psi_decomposition_of_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:05:20.420163+00:00
-- url     : https://prove2.me/submissions/5413c963-8d76-4229-9730-bb97ddd181eb

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_joint_smalltime_triplet_data
import Theorems.Thm_levy_foundations_public_semigroup_smallball_variance_bound
import Theorems.Thm_levy_foundations_public_semigroup_psi_integral_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

/-- Extract the triplet by the same joint-limit, Gaussian correction and
compensated exponent identity used in the original LeanLevy assembly. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ),
      ProbabilityTheory.IsLevyMeasure ν ∧
      ∀ ξ : ℝ,
        S.exponent ξ = ↑b * ↑ξ * Complex.I
          - ↑(σ_sq : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral ν
              (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) := by
  obtain ⟨r, b_r, σ_sq_r, ν, hν, t_seq, hr, hν_r, ht, hb, hσ, h_jump⟩ :=
    levy_foundations_public_semigroup_joint_smalltime_triplet_data S
  refine ⟨b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν,
    Real.toNNReal ((σ_sq_r : ℝ) -
      ∫ x in {x | |x| < r}, x ^ 2 ∂ν), ν, hν, ?_⟩
  intro ξ
  have hr_pos : (0 : ℝ) < r := by linarith [hr.1]
  have hnn : (0 : ℝ) ≤ (σ_sq_r : ℝ) -
      ∫ x in {x | |x| < r}, x ^ 2 ∂ν := by
    have hle := levy_foundations_public_semigroup_smallball_variance_bound
      S hr_pos hν hν_r hσ h_jump
    linarith
  rw [show (↑(Real.toNNReal ((σ_sq_r : ℝ) -
      ∫ x in {x | |x| < r}, x ^ 2 ∂ν)) : ℝ) =
      (σ_sq_r : ℝ) -
        ∫ x in {x | |x| < r}, x ^ 2 ∂ν from
        Real.coe_toNNReal _ hnn]
  exact levy_foundations_public_semigroup_psi_integral_identity
    S hr b_r σ_sq_r hν hν_r ht hb hσ h_jump ξ
