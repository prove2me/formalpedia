-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_rank_one_trace_product
-- name    : Conway99Formal.CubicMetric.rank_one_trace_product
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:55:31.311551+00:00
-- url     : https://prove2.me/theorems/a56e313a-4e5f-45bc-826a-93cf5105943f
-- title:
--   Trace product for rank-one sums
-- statement:
--   If $F_{ij}=-\frac13\sum_ta_t\tau_t(i)\tau_t(j)$ and $H_{ij}=-\frac13\sum_tb_t\tau_t(i)\tau_t(j)$ for finite arrays, then $9\operatorname{tr}(FH)=\sum_{t,u}a_t(\sum_i\tau_t(i)\tau_u(i))^2b_u$.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/TraceForm.lean#30-80; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 41886149af07dad84a52c54e70937fec064d5fb5f17c883bb4aea3e7935a19b3. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/TraceForm.lean#L30-L80.

import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.rank_one_trace_product {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq I] (tau : T → I → ℝ) (a b : T → ℝ)
    (F H : Matrix I I ℝ)
    (hF : ∀ i j, F i j = -(∑ t, a t * tau t i * tau t j) / 3)
    (hH : ∀ i j, H i j = -(∑ t, b t * tau t i * tau t j) / 3) :
    9 * Matrix.trace (F * H) =
      ∑ t, ∑ u, a t * (∑ i, tau t i * tau u i) ^ 2 * b u := by sorry
