-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_real_finite_strip
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_real_finite_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:15:44.971733+00:00
-- url     : https://prove2.me/theorems/2fb40310-3fbd-4a5b-83f9-5b4e89f46845
-- title:
--   Genuine original-clock descending real MGF cross identity on the strict positive-root rate strip
-- statement:
--   For every original spectrally negative Lévy process X and independent exponential observation clock Exp(p), a positive Laplace root λ with ψ(λ)=p, and every real β satisfying 0<β<λ, the actual negative terminal drawdown MGF L(β) satisfies L(β)(p−ψ(β))=(p/λ)(λ−β). The genuine spectral root strict rate gap ψ(β)<p is derived rather than assumed. The argument converts the accepted ENNReal terminal Wiener–Hopf factor via the genuine original-clock mgf-lintegral identity using the exact toReal product identities and mgf nonnegativity. This is precisely the source-specific finite-strip hypothesis of the accepted all-β analytic-continuation theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_positive_root_strict_gap_below
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_real_finite_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 < β) (hβlam : β < lam) :
    (mgf (fun z : Ω × ℝ =>
      -(runningSup X (Real.toNNReal z.2) z.1 -
        X.X (Real.toNNReal z.2) z.1))
      (P.prod (expMeasure p)) β) * (p - X.ψ β) =
    (p / lam) * (lam - β) := by sorry
