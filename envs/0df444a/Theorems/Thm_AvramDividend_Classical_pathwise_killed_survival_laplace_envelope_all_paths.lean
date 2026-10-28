-- Prove2me | Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_laplace_envelope_all_paths
-- name    : AvramDividend.Classical.pathwise_killed_survival_laplace_envelope_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:33:33.470634+00:00
-- url     : https://prove2.me/theorems/297cb020-b35b-4b9b-a2d2-51f4ef652cf5
-- title:
--   Closed-horizon killed-survival reserve Laplace envelope for every Lévy sample path
-- statement:
--   For each finite horizon, every sample path of a spectrally negative Lévy process has a finite running infimum, and the Laplace transform of initial reserves surviving to that horizon is an exponential of the reflected infimum divided by θ. The finite-horizon lower boundedness theorem removes the explicit pathwise lower-bound assumption of the already Proved reserve-integral identity. This is the exact inner integral required by a Tonelli computation of the killed survival resolvent.
-- source:
--   Proved pathwise_killed_survival_reserve_laplace_envelope and direct levy_path_bddBelow_finite_horizon.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_reserve_laplace_envelope

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.pathwise_killed_survival_laplace_envelope_all_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω},
        Real.exp (-θ * x)) =
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ := by sorry
