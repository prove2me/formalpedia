-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_rank_one_covariance
-- name    : Conway99Formal.CubicMetric.rank_one_covariance
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:55:18.18924+00:00
-- url     : https://prove2.me/theorems/b92e0f28-d98b-4244-a369-b04b73d12065
-- title:
--   Covariance sum from frame correlations
-- statement:
--   For finite index sets, assume $F_u(i,j)=-\frac13\sum_t h_u(t)\tau_t(i)\tau_t(j)$ and $\sum_u h_u(t)h_u(s)=63\sum_k\tau_t(k)\tau_s(k)$. Then $\sum_uF_u^2=7[\sum_{t,s}(\sum_k\tau_t(k)\tau_s(k))^2\tau_t(i)\tau_s(j)]_{ij}$. Both assumptions are explicit.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/TraceForm.lean#91-202; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 41886149af07dad84a52c54e70937fec064d5fb5f17c883bb4aea3e7935a19b3. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/TraceForm.lean#L91-L202.

import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.rank_one_covariance {U T I : Type*} [Fintype U] [Fintype T]
    [Fintype I] [DecidableEq I] (tau : T → I → ℝ) (h : U → T → ℝ)
    (F : U → Matrix I I ℝ)
    (hF : ∀ u i j, F u i j = -(∑ t, h u t * tau t i * tau t j) / 3)
    (hpair : ∀ t s,
      (∑ u, h u t * h u s) = 63 * (∑ k, tau t k * tau s k)) :
    (∑ u, F u * F u) =
      (7 : ℝ) • Matrix.of (fun i j =>
        ∑ t, ∑ s, (∑ k, tau t k * tau s k) ^ 2 * tau t i * tau s j) := by sorry
