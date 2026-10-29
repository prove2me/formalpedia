-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_gap_descending_unscaled
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_gap_descending_unscaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:14:29.534659+00:00
-- url     : https://prove2.me/theorems/bcbaca2c-7cd5-45bf-ba35-28b087b692f6
-- title:
--   Genuine original-clock descending drawdown Laplace value in the strict moment gap
-- statement:
--   Under the actual original spectrally negative Lévy law and independent Exp(p) clock, for a strictly positive root lam of ψ(lam)=p and 0≤β<lam with ψ(β)<p, the actual terminal drawdown negative-Laplace integral equals ofReal((p/lam)*((lam−β)/(p−ψ(β)))). Both denominators are strictly positive, so cancellation from the previously accepted genuine crossed factor is legitimate in the extended nonnegative reals.
-- source:
--   Immediate source-faithful unscaled corollary of accepted original exponential-clock descending finite-gap cross-factor 3d509051-cdde-474a-95ac-a3eb59dd3972. Supplies the exact transform to the WS1A/WS1B killed-resolvent work without assuming moments or artificial independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_laplace_crossmul

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_gap_descending_unscaled
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 ≤ β) (hβlam : β < lam)
    (hgap : X.ψ β < p) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal ((p / lam) * ((lam - β) / (p - X.ψ β))) := by sorry
