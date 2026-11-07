-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_eq_8_threshold
-- name    : CorrelatedLocalSearch.eq_8_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:19.636959+00:00
-- url     : https://prove2.me/theorems/2a6843df-d0c8-4538-ab56-5e1af2f3a35f
-- title:
--   (8) — $\lambda>1$, $s_*\in(0,1)$, and $a=rk^{-s_*}=\lambda/2$, $b=(k-r)k^{-s_*}=1/(2\lambda)$
-- statement:
--   Let $k,r$ be integers with $k/2<r<k$, and let $\lambda=\sqrt{r/(k-r)}$ and $s_*=\log_k(2\sqrt{r(k-r)})$. Then
--   $$
--   \lambda>1,\qquad 0<s_*<1,\qquad r\,k^{-s_*}=\frac{\lambda}{2},\qquad (k-r)\,k^{-s_*}=\frac{1}{2\lambda}.
--   $$
--
--   The last two identities say that at the threshold the cover-sum weights of decreasing and increasing symbols become $\lambda/2$ and $1/(2\lambda)$, so that after rescaling by $\lambda^d$ the comparison is a symmetric simple random walk.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §4, eq. (8), p.9 (PDF p.11); App. C.1, proof of Lemma C.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- (8) and the weights `a, b` (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), §4, eq. (8), p.9, and App. C.1, proof of Lemma C.1,
p.21): for integers `k/2 < r < k`, `λ = √(r/(k−r)) > 1`, `s∗ = log_k(2√(r(k−r))) ∈ (0, 1)`,
and `a = r k^{−s∗} = λ/2`, `b = (k−r) k^{−s∗} = 1/(2λ)`.

**Formalization Note** `k/2 < r` is written `k < 2 * r`. -/
theorem eq_8_threshold (k r : ℕ) (hk : k < 2 * r) (hr : r < k) :
    1 < lam k r ∧ 0 < sStar k r ∧ sStar k r < 1 ∧
      (r : ℝ) * (k : ℝ) ^ (-sStar k r) = lam k r / 2 ∧
      ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) = 1 / (2 * lam k r) := by sorry

end CorrelatedLocalSearch
