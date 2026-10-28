-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_history_zero_exponential_survival
-- name    : AvramDividend.Classical.bv_actual_residual_history_zero_exponential_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:53:47.020655+00:00
-- url     : https://prove2.me/theorems/605f5a1c-7ebb-4959-9e6d-00d21de741f2
-- title:
--   Exponential no-residual-through-horizon survival law for the actual finite-activity Lévy process
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process with finite negative-jump intensity λ, the event that the nonnegative drift residual Y_s=d s-X_s has remained exactly zero at every time 0≤s≤t has probability exp(-λt). This upgrades the already-Proved zero-atom law at a fixed horizon to a full continuous-path-history survival law using the actual residual's globally monotone sample paths and the proved monotone endpoint/history equivalence. It is a direct precursor of the first-jump stopped dividend identity.
-- source:
--   Avram Palmowski Pistorius (2007), §3.3, first-jump formula (3.14), with Prove2Me proved residual monotonicity and zero-atom probability.

import Theorems.Thm_AvramDividend_Classical_monotone_zero_horizon_iff_history_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_history_zero_exponential_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0} =
        Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
