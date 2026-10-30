-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierValue_esscher_upper_bound
-- name    : AvramDividend.Classical.avram_root29_05_barrierValue_esscher_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:13:37.424598+00:00
-- url     : https://prove2.me/theorems/60669816-f310-4cc0-9607-0b28c8da083c
-- title:
--   Original reflected dividend value bounded by Esscher exponential distance to the barrier
-- statement:
--   Given a positive Esscher root φ with ψ(φ)=q>0, the true expected discounted killed reflected-regulator dividend value at 0≤x≤a is bounded by exp(-φ(a-x)) times the original true value at the barrier. The upper bound uses the genuine original Lévy law and strict stopped regulator, not a scale quotient.
-- source:
--   The exact canonical Proved actual dividend value factorisation 8fc83520 gives the stopped strict two-sided exit expectation multiplier times barrierSupValue. The Proved equivalence caca9b2f relates the original strict exit factor to its corrected form, and the Proved Esscher-root bound a6c37169 bounds that coefficient by exp(-φ(a-x)). Multiply the ENNReal inequality by the same nonnegative true reflected boundary dividend value; no unproved scale ratio is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_barrierValue_esscher_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) *
        barrierSupValue X a q := by sorry
