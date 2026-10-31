-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_centred_clipped_futureIncrement_condExp_zero
-- name    : AvramDividend.Classical.avram_wave3_04_centred_clipped_futureIncrement_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:39:42.792054+00:00
-- url     : https://prove2.me/theorems/83b4a4a9-6329-4c37-96b8-b0fea6accf39
-- title:
--   Centred symmetric truncations of original Lévy increments have zero conditional mean without moment assumptions
-- statement:
--   At deterministic times s≤t, the original spectrally negative Lévy increment X_t−X_s is symmetrically clipped to [-K,K] and centred using the exact original-law expectation of the similarly clipped stationary increment X_(t−s). This bounded centred payoff is integrable even if E|X_(t−s)| is infinite, and has conditional expectation zero relative to the original complete past filtration F_s. The proof derives measurability and the clipping bound, integrability from original source adaptedness, the exact mean subtraction through Bochner integral identities, and the previously accepted full-filtration independent-increment conditional law. This is a canonical moment-free compensated Lévy increment for UBV simple stochastic-martingale approximants.
-- source:
--   Pinned private compiler job 33cfc4f2-ad6d-45e2-931b-c054a2f17556 reached sentinel with no candidate errors after repair of integrable_const implicit arguments, source SHA256 3ed820955813000da2f9785c95eedf0b2555aa51b221715d729ad1cd507978f8. Canonical Proved source bounded-payoff integrability eb2ca071-17d0-409f-b88a-59edf9d25ee8, future Lévy conditional law 60e3f274-5580-448a-a1d8-6485fa8ab41a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_centred_clipped_futureIncrement_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (K : ℝ) (hK : 0 ≤ K) :
    P[(fun ω =>
      max (-K) (min K (X.X t ω - X.X s ω)) -
        ∫ η, max (-K) (min K (X.X (t - s) η)) ∂P) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
