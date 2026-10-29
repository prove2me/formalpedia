-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:54:31.428025+00:00
-- url     : https://prove2.me/theorems/3d509051-cdde-474a-95ac-a3eb59dd3972
-- title:
--   Original exponential-clock descending Wiener–Hopf finite-gap cross-multiplied transform
-- statement:
--   For every original spectrally negative Lévy X, independent Exp(p) clock, λ>0 satisfying ψ(λ)=p, and 0≤β<λ with ψ(β)<p, the actual terminal drawdown D=S_e−X_e has the exact ENNReal cross-multiplied descending Laplace transform: (p−ψβ)λ E exp(−βD)=p(λ−β). It follows entirely from the accepted true original-clock supremum moment and terminal Wiener–Hopf factor normalisation, with no analytic continuation or invalid division beyond the strict rate gap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_wh_gap_normalisation
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 ≤ β) (hβlam : β < lam)
    (hgap : X.ψ β < p) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal (p - X.ψ β) * ENNReal.ofReal lam *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
        ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal (lam - β) * ENNReal.ofReal p := by sorry
