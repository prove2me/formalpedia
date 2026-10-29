-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_root_descending_scaled
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_root_descending_scaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:19:28.931812+00:00
-- url     : https://prove2.me/theorems/592fbcaf-38ad-40d5-b3b4-fb62807bdec2
-- title:
--   Actual original-clock descending factor at the removable positive exponent root, scaled
-- statement:
--   Under the actual original product P×Exp(p+q) law and genuinely time-dependent positive-q Esscher density, the terminal drawdown Laplace transform at β=φ+λ satisfies the exact removable-root scaled identity a p E exp(-aD)= (p+q) λ p/(λm), where a=φ+λ and m=ψ′(a)>0. This is the source-specific exact root branch; no division by p+q−ψ(a)=0 is used.
-- source:
--   Combines the accepted actual inverse joint-clock all-real drawdown factor 5f48ee29, actual tilted supremum exponential law 1a8d4fdc at −φ, and the separately accepted derivative-value branch at δ=λ of the genuine tilted descending all-positive transform e4e12a00. Completes the singular root point for the original descending resolvent factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_root_descending_scaled
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ENNReal.ofReal (φ + lam) *
      (ENNReal.ofReal p *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (-(φ + lam) *
              (runningSup X (Real.toNNReal z.2) z.1 -
                X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure (p + q))))) =
    ENNReal.ofReal (p + q) *
      (ENNReal.ofReal lam * ENNReal.ofReal (p / (lam * m))) := by sorry
