-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_two_sided_stopped_scale_martingale
-- name    : AvramDividend.Classical.bv_two_sided_stopped_scale_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T02:12:52.325212+00:00
-- url     : https://prove2.me/theorems/5955d9a2-224d-4fe7-acf9-fc1fbb015da5
-- title:
--   BV two-sided stopped discounted q-scale process is a martingale
-- statement:
--   For a bounded-variation spectrally negative Levy process with standing assumptions and q-scale function W, the discounted scale process stopped at the first two-sided exit (up-exit above a-x or down-exit below -x), M_t = exp(-q (t wedge tau)) * W(x + X_{t wedge tau}), is a martingale. This isolates the missing stopped-martingale obligation (a) behind the BV stopped-scale balance 2bb529c8: with optional-stopping applicability (b) and the proved killed-exit vanishing pieces, it yields the balance and hence the 3e1ce2c8/5bcf90e1 chain.
-- source:
--   Missing stopped-martingale obligation (a) from the BV-route analysis of 2bb529c8: the unbounded unstopped analogue is Open d38b09a0 and the unstopped form is Proved impossible in UBV (0fc74c47), so the BV stopped form is formulated as an independent child using only codebase-attested idioms (exit-time toReal/toNNReal from f2638d8a, Martingale shape from d38b09a0). No theorem premises cited, so no dependency cycle.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_two_sided_stopped_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    Martingale (fun t : ℝ≥0 => fun ω =>
      Real.exp (-(q * (min (t : ℝ≥0∞)
        (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))).toReal)) *
        W (x + X.X (min (t : ℝ≥0∞)
          (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))).toNNReal ω)) 𝓕 P := by sorry

end AvramDividend.Classical
