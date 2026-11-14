-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_positive_clock_zero_contact_predividend_leftLim_zero
-- name    : AvramDividend.Classical.avram_bvb25_original_positive_clock_zero_contact_predividend_leftLim_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:54:15.116504+00:00
-- url     : https://prove2.me/theorems/f305c039-9eae-461f-9b95-dc48bf829e72
-- title:
--   Original zero-contact physical prepayment left reserve vanishes at every strictly positive source clock with no auxiliary topology assumption
-- statement:
--   For the actual original BV no-negative-jump linear-drift source with original controlled reserve zero through the observation horizon, at every strictly positive original physical time up to that horizon the prepayment left reserve used inside the complete negative-mark K compensator is zero. The previously accepted source transport requires a nontrivial strict left neighbourhood; positive NNReal time provides one automatically via pinned Mathlib. This removes the extra topology premise and directly matches the source stopped-K guard 0<t on its true time/mark domain, eliminating the zero-contact boundary ambiguity.
-- source:
--   Accepted source prepayment lemma 810c78f4, pinned Mathlib nhdsLT_neBot_of_exists_lt with physical 0<t, original K integrand in ed067740.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb25_original_positive_clock_zero_contact_predividend_leftLim_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t = 0 := by sorry
