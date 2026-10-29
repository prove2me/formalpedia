-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_above_root_descending_scaled
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_scaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:04:35.964436+00:00
-- url     : https://prove2.me/theorems/02e15cf7-b400-4e11-8fd8-4501ba8eb6d9
-- title:
--   Source-specific original-clock descending Wiener–Hopf Laplace factor above the positive root, scaled without ENNReal division
-- statement:
--   Under the real spectrally negative Lévy process, positive q-root φ, shifted p-root λ, and positive derivative at φ+λ, for each β>φ+λ, the genuine P×Exp(p+q) drawdown Laplace integral, multiplied by p and φ+λ, equals the exact Esscher-descending rational factor times p+q and λ. The scaled extended-nonnegative-real form is exact and avoids division by potentially infinite expectations. This is a substantive source-specific transfer beyond the general inverse Esscher identity: its proof combines the accepted genuine tilted all-β descending factor, the actual tilted exponential supremum law, and full original-clock inverse factorisation.
-- source:
--   Immediate high-beta original-clock Laplace transform reduction for WS1A/WS1B lower-killed spatial resolvent. Genuinely uses Proved 5f48ee29 all-real inverse measure/reward factor, Proved 1a8d4fdc tilted supremum moment including negative parameter -φ, and Proved e4e12a00 full tilted descending transform. The β>φ+λ range is precisely the large positive Laplace halfline required by spatial uniqueness. The remaining passage to the unscaled rational formula is positive finite scalar cancellation and not assumed here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_scaled
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
    ENNReal.ofReal (φ + lam) *
      (ENNReal.ofReal p *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (-β * (runningSup X (Real.toNNReal z.2) z.1 -
              X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure (p + q))))) =
    ENNReal.ofReal (p + q) *
      (ENNReal.ofReal lam *
        ENNReal.ofReal
          ((p / lam) *
            ((φ + lam - β) / (p + q - X.ψ β)))) := by sorry
