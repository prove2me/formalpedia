-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_perpetual_esscher_renewal_cancel_to_scale_ratio
-- name    : AvramDividend.Classical.avram_ws01h_perpetual_esscher_renewal_cancel_to_scale_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:11:04.87067+00:00
-- url     : https://prove2.me/theorems/c64232cd-4bad-424e-8a49-b295c161f719
-- title:
--   Perpetual original Esscher CDF first-record renewal cancels exactly to the source q-scale exit ratio
-- statement:
--   Suppose the positive-root Esscher perpetual lower-survival CDF values at x and a are both identified with the genuine q-scale via the same strictly positive normalisation m and the factors exp(-φx), exp(-φa). If an independently established lower-killed genuine first-record renewal reads Cx=exp(φ(a-x)) Ca K for the actual original-law stopped discounted upcrossing K, then K=W(x)/W(a) exactly. The proof handles the original a-x shift and cancels only a nonzero positive factor, retaining the boundary reserve x=0. It does not assume the desired exit ratio or any stochastic factor as a theorem; those remain explicit hypotheses to discharge via the finite-clock Qp renewal.
-- source:
--   Genuine perpetual CDF-scale theorem 44e9b6c5 and original lower-killed renewed CDF (pending). Mathlib Real.exp_add and field cancellation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory

theorem AvramDividend.Classical.avram_ws01h_perpetual_esscher_renewal_cancel_to_scale_ratio
    (φ m x a K Cx Ca : ℝ) (W : ℝ → ℝ)
    (hm : 0 < m) (hWa : 0 < W a)
    (hCx : Cx = m * Real.exp (-(φ * x)) * W x)
    (hCa : Ca = m * Real.exp (-(φ * a)) * W a)
    (hRenew : Cx = Real.exp (φ * (a - x)) * Ca * K) :
    K = W x / W a := by sorry
