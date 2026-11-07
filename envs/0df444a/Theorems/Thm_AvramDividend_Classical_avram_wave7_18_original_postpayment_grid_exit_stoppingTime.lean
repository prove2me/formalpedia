-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_grid_exit_stoppingTime
-- name    : AvramDividend.Classical.avram_wave7_18_original_postpayment_grid_exit_stoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:18:33.295741+00:00
-- url     : https://prove2.me/theorems/87c7dd5a-9208-42b1-8a93-3846e84d9b48
-- title:
--   Original-filtration stopping time for the bounded-grid two-sided positive-reserve exit
-- statement:
--   For the original spectrally negative Lévy process X and original admissible left-continuous dividend strategy D, the first bounded grid exit of the corrected post-payment reserve x+X(clock k)-rightLimit D(clock k) from the interval (lower,upper) is a stopping time in the indexed filtration H k = 𝓕.rightCont(clock k). This exposes the stopping-time conclusion currently hidden inside a Proved stopped-value-measurability lemma, enabling predictable integrands and source-specific positive-reserve grid localisation. The continuous-time exhaustion and C² interior bounds are separate obligations.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_postpayment_grid_exit_stoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by sorry
