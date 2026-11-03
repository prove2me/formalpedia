-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_L2_variance_stationarity
-- name    : AvramDividend.Classical.avram_wave7_06_original_centered_future_L2_variance_stationarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:40:37.263206+00:00
-- url     : https://prove2.me/theorems/9b9e9f4c-bb17-4c8b-bdbc-adb618faa720
-- title:
--   Original mean-centred future Lévy increments have finite and stationary second moments
-- statement:
--   Original source integrability of X_t and X_t² implies integrability of the square of the shifted future increment centred by E[X_t]; this centred second moment is independent of start time s and equals the centred second moment of X_t. The proof composes genuine source-specific L² integrability and IdentDistrib, not an auxiliary Poisson/Brownian law.
-- source:
--   W7-06 original future centred variance control for L² truncation/martingale estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_centered_future_L2_variance_stationarity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hFirst : Integrable (X.X t) P)
    (hSecond : Integrable (fun ω => (X.X t ω)^2) P) :
    Integrable (fun ω =>
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P))^2) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω -
      (∫ η, X.X t η ∂P))^2 ∂P) =
      (∫ ω, (X.X t ω -
        (∫ η, X.X t η ∂P))^2 ∂P) := by sorry
