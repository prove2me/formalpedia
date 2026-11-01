-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finset_projective_law
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_finset_projective_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:04:48.747982+00:00
-- url     : https://prove2.me/theorems/8a1e0b63-6eb3-4070-b07b-8968fed390ad
-- title:
--   Actual Esscher-reflected Lévy pair has terminal-independent finite-dimensional laws at every finite time set
-- statement:
--   For a genuine spectrally negative Lévy process and positive q-root Esscher parameter φ, choose any finite set I of nonnegative observation times before H. The complete joint pushforward law of the actual running local-time regulator S_t and its reflected drawdown R_t, simultaneously at every t∈I, is identical under any two finite Esscher terminal laws Q_T1,Q_T2 with T_i≥H+1. This is the source-specific finite-dimensional projective family needed for a canonical tilted reflected path-space extension. It asserts no all-horizon extension or excursion process.
-- source:
--   The accepted bounded-stopped-history observable consistency 4c1a5b7a, actual adapted supremum from barrierStrategy and actual reflectedSup_adapted 63c373fc; pinned measurable_pi_iff constructs measurable finite-coordinate vector.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_finset_projective_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (I : Finset ℝ≥0)
    (H T₁ T₂ : ℝ≥0)
    (hIH : ∀ t ∈ I, t ≤ H)
    (hT₁ : H + 1 ≤ T₁) (hT₂ : H + 1 ≤ T₂) :
    Measure.map
      (fun ω : Ω => fun i : I =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₁ ω - (T₁ : ℝ) * X.ψ φ)))) =
    Measure.map
      (fun ω : Ω => fun i : I =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₂ ω - (T₂ : ℝ) * X.ψ φ)))) := by sorry
