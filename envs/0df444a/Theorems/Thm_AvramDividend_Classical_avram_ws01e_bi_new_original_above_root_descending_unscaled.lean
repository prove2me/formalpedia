-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_above_root_descending_unscaled
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_unscaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:23:29.295817+00:00
-- url     : https://prove2.me/theorems/216e2404-a1e9-41df-9c5f-0db8d31dc0e8
-- title:
--   Exact genuine original-clock descending Laplace value above the Lévy positive root
-- statement:
--   For an actual spectrally negative Lévy process with positive q-root φ, positive shifted p-root λ and positive derivative m at φ+λ, under the genuine independent original exponential clock Exp(p+q), for every β>φ+λ the drawdown Laplace transform equals the exact ENNReal.ofReal of ((p+q)/(φ+λ)) * ((φ+λ−β)/(p+q−ψ β)). The right-side quotient is well-defined in real arithmetic in this range by genuine strict above-root exponent monotonicity. This exact unscaled result follows from the Proved scaled identity by cancellation of the strictly positive finite real factor (φ+λ)p.
-- source:
--   Corollary of canonically Proved full actual original-clock high-beta scaled factor 02e15cf7-b400-4e11-8fd8-4501ba8eb6d9, accepted candidate 18046, with explicit positive nonzero finite ENNReal cancellation. Supplies a directly usable descending transform on the large spatial-Laplace halfline for the WS1A/WS1B killed-resolvent proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_above_root_descending_scaled

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_unscaled
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m β : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hβ : φ + lam < β)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure (p + q)))) =
    ENNReal.ofReal
      (((p + q) / (φ + lam)) *
        ((φ + lam - β) / (p + q - X.ψ β))) := by sorry
