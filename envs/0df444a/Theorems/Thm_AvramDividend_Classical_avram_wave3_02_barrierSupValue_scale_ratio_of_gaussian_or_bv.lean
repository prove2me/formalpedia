-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
-- name    : AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:29:26.174492+00:00
-- url     : https://prove2.me/theorems/f5d1d5b0-f8a0-4b9f-8203-c46ed49d1167
-- title:
--   Genuine reflected barrier scale ratio in the Gaussian and BV branches
-- statement:
--   For the actual reflected supremum dividend regulator and the genuine q-scale function, at any positive barrier a the discounted regulator value is ENNReal.ofReal(W(a)/W'(a)) under Standing and q>0 whenever the Lévy process has a Gaussian part or bounded variation. This is a source-level stochastic valuation theorem; no pure-jump regularity is assumed.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 1, and Kuznetsov–Kyprianou–Rivero review. It uses the canonical Proved Gaussian/BV derivative positivity a3226a42 and the genuine Proved stopped-renewal lower/upper bounds 6b821aa5 and c6c3b1d0 plus the Proved exact converter 3c69ef7b. This is a noncircular Gaussian/BV branch of canonical Open barrierSupValue_eq_scale_ratio a8d4c941.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by sorry
