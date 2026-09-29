-- Prove2me | Theorems.Thm_CandesTao_LowerBound_I20_implies_I21
-- name    : CandesTao.LowerBound.I20_implies_I21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:45:15.659717+00:00
-- url     : https://prove2.me/theorems/9c8e8089-a76c-4461-9ead-aa58591a4502
-- title:
--   Theorem 1.7, second part — (I.20) implies (I.21)
-- statement:
--   Fix integers $1 \le m$ and $1 \le r \le n$, a real $\mu_0 \ge 1$ and $0 < \delta < 1/2$, and let $\epsilon := \frac12\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)$ (natural logarithm). If
--
--   $$m \ge n^2\left(1 - e^{-\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)}\right) \qquad \text{(I.20)}$$
--
--   then
--
--   $$m \ge (1-\epsilon)\,\mu_0 n r\log\left(\frac{n}{2\delta}\right). \qquad \text{(I.21)}$$
--
--   Equivalently, if (I.21) fails then (I.20) fails. This is the second part of Theorem 1.7 of Candès and Tao: the lower bound stated under the failure of (I.20) applies in particular whenever the easier-to-read condition (I.21) fails.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2058, Theorem 1.7 ((I.20), (I.21)); p. 2060, Section II ('The second part of the theorem, namely, (I.21) follows from 1 − e^{−x} > x − x²/2 whenever x ≥ 0')

import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem I20_implies_I21
    (n m r : ℕ) (μ₀ δ : ℝ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : SamplingConditionI20 n m r μ₀ δ) :
    SamplingConditionI21 n m r μ₀ δ := by sorry

end CandesTao.LowerBound
