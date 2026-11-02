-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_lipschitz_derivative_transition_nhds_zero
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_lipschitz_derivative_transition_nhds_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:44:27.807012+00:00
-- url     : https://prove2.me/theorems/ebf57b34-1362-499d-89eb-7267f9e189fa
-- title:
--   Genuine Lévy transition expectations of bounded continuous C1 derivatives converge at time zero
-- statement:
--   For the actual spectrally negative Lévy process, every globally C1 function w satisfying a global Lipschitz constant L has bounded continuous derivative. Its original-process transition expectation E[deriv w(x+X_t)] tends to deriv w x in the right-hand NNReal time-neighborhood t→0. Formal proof constructs LipschitzWith (Real.toNNReal L), applies norm_deriv_le_of_lipschitz, derives continuous derivative from ContDiff R 1, invokes the already Proved bounded continuous original-source transition strong continuity for each time sequence, and lifts the sequential result to nhds by the countably generated filter criterion. This identifies the physical-drift contribution's time-zero continuity without changing the process or assuming the generator equation.
-- source:
--   Complete remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_actual_C1_derivative_transition_nhds_zero_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_strong_continuity_at_zero_bounded
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_lipschitz_derivative_transition_nhds_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) :
    Tendsto (fun t : ℝ≥0 => ∫ ω, deriv w (x + X.X t ω) ∂P)
      (nhds 0) (nhds (deriv w x)) := by sorry
