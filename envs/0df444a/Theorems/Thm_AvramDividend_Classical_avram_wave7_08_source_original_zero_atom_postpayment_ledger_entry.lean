-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
-- name    : AvramDividend.Classical.avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:40:33.719721+00:00
-- url     : https://prove2.me/theorems/e6bfefd9-5fb0-4fed-8080-cee8247f98b7
-- title:
--   Exact source time-zero postpayment value plus initial dividend right atom fits w(initial capital)
-- statement:
--   The corrected initial-atom HJB secant hypothesis at t=0, original X(0)=0 and original D(0)=0 imply w(x−D(0+))+D(0+)≤w(x) on every sample ω. This is the source-specific entry condition for the finite original discounted postpayment Itô–Meyer ledger, including a positive initial lump sum and w(0)≥0 where relevant. It does not assume a different model or remove the time-zero atom.
-- source:
--   Original W7-08 corrected hjump and IsAdmissibleLe. Provides hinit for W7-08 finite mesh ledger once its first clock is zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    w (x - rightLimit D 0 ω) + rightLimit D 0 ω ≤ w x := by sorry
