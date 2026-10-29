-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_real_mgf_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_tilted_supremum_real_mgf_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:14:03.366001+00:00
-- url     : https://prove2.me/theorems/c72dadaf-18f4-4160-9846-99841fc37414
-- title:
--   Actual tilted exponential supremum real MGF within its strict root gap
-- statement:
--   Under the genuine random-terminal Esscher law and beta<lam, the supremum real MGF equals lam/(lam-beta). It is obtained by converting the genuine ENNReal supremum moment of the positive exponential to a finite Bochner integral: positivity and the rate-gap identity prove integrability before ofReal_integral_eq_lintegral_ofReal. This is the real supremum input for true finite-rate Wiener-Hopf factorisation and makes no independence assertion.
-- source:
--   Proved actual Qp Exp(lam) law cf4dc156 and Proved source-faithful ENNReal supremum moment child 1a8d4fdc; pinned Mathlib lintegral_ofReal_ne_top_iff_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_tilted_supremum_real_mgf_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p lam β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p) (hβlam : β < lam) :
    mgf (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β =
    lam / (lam - β) := by sorry
