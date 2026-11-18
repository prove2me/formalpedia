-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_marked_joint_PGF_real_entire_HasSum_20261117
-- name    : AvramDividend.Classical.avram_a27_original_marked_joint_PGF_real_entire_HasSum_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:50:31.780695+00:00
-- url     : https://prove2.me/theorems/f7e20ed5-ab0c-4923-a6e7-729fe49aa6b1
-- title:
--   Entire-real count generating series for actual finite-activity original physical marked negative jumps
-- statement:
--   For an original spectrally negative Levy process with finite negative-jump intensity, the source-space marked generating function E[z^{K_t}exp(theta J_t)] has an exact count-cell power series for every real z, including z outside [0,1]. The physical negative jump exponential is bounded by one; the true count K_t has the prescribed Poisson(r) law and hence its absolute real powers are integrable. This gives global convergence of the original physical marked count series without any independent mark-stream assumptions.
-- source:
--   Pinned MeasurePreserving.integrable_comp_of_integrable and Integrable.mono; Proved source A85, Poisson geometric integrability 8ad7cf40, and exact count-cell HasSum ac27bb3.

import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_real_geometric_sequence_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_marked_joint_PGF_real_entire_HasSum_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P))
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by sorry
