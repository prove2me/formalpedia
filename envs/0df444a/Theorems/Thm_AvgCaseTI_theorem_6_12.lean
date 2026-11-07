-- Prove2me | Theorems.Thm_AvgCaseTI_theorem_6_12
-- name    : AvgCaseTI.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:42.399735+00:00
-- url     : https://prove2.me/theorems/a4089c44-a3c6-45d4-8d87-af01452991a3
-- title:
--   Theorem 6.12 — eigenvalue-free invertible matrices with prescribed $\mathrm{Tr}(A^2)$
-- statement:
--   Let $\mathbb F_q$ be a finite field and, for $k\in\mathbb F_q$, $\beta(n,q,k)$ the probability that a uniform $A\in\mathrm{GL}(n,q)$ is eigenvalue-free in $\mathbb F_q$ and has $\mathrm{Tr}(A^2)=k$. Then for every $k$ the limit $\beta(\infty,q,k)=\lim_n\beta(n,q,k)$ exists and
--   $$
--   \beta(\infty,q,k)=\frac1q\,v(\mathrm{GL},\infty,q)=\frac1q\,c(q)^{q-1},
--   $$
--   where $v(\mathrm{GL},\infty,q)=\lim_n v(\mathrm{GL},n,q)$. Moreover, for every $n>5(q-1)^2$ and every $k\in\mathbb F_q$,
--   $$
--   |\beta(\infty,q,k)-\beta(n,q,k)|\le\Gamma(n,q),
--   $$
--   with $\Gamma(n,q)$ the explicit error term defined with $\beta$.
--
--   So the value of $\mathrm{Tr}(A^2)$ is asymptotically uniform on eigenvalue-free matrices, with an explicit rate; Theorem 6.11 is derived from it.
--
--   **Formalization Note** The statement includes $\lim_n v(\mathrm{GL},n,q)=c(q)^{q-1}$, so that both printed expressions for $\beta(\infty,q,k)$ are present.
--
--   Differences from the source:
--
--   - encoding: a statement "lim x(n) = L" → `Tendsto x atTop (𝓝 L)` → same statement; reason: Lean convention
--   - encoding: c(q) = lim c_n(q) (an infinite product) → `cInf q`, the infimum of the decreasing positive partial products → same value; reason: Lean convention
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.12, Eq. (54), p.43 (PDF p.45)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_vGL
import Definitions.Def_AvgCaseTI_betaProb

set_option autoImplicit false

namespace AvgCaseTI

open Filter Topology

/-- **Theorem 6.12 (eigenvalue-free invertible matrices with prescribed `Tr(A²)`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.12, p.43
(PDF p.45): for every finite field with `q` elements and every `k ∈ F_q`, the limit
`β(∞, q, k) = lim β(n, q, k)` exists and equals `(1/q)·v(GL, ∞, q) = (1/q)·c(q)^{q−1}`; and for every
`n > 5(q − 1)²` and every `k`, `|β(∞, q, k) − β(n, q, k)| ≤ Γ(n, q)` (Eq. (54)).

**Formalization Note.** The first clause records `v(GL, ∞, q) = lim v(GL, n, q) = c(q)^{q−1}`, so
that both printed expressions for `β(∞, q, k)` are present; `Γ(n, q)` is `GammaBound q n`. -/
theorem theorem_6_12 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    Tendsto (vGL K) atTop (𝓝 (cInf q ^ (q - 1))) ∧
    (∀ k : K, Tendsto (fun n => betaProb K n k) atTop (𝓝 (1 / (q : ℝ) * cInf q ^ (q - 1)))) ∧
    ∀ n : ℕ, 5 * (q - 1) ^ 2 < n → ∀ k : K,
      |1 / (q : ℝ) * cInf q ^ (q - 1) - betaProb K n k| ≤ GammaBound q n := by sorry

end AvgCaseTI
