-- Prove2me | Theorems.Thm_AvgCaseTI_theorem_6_5
-- name    : AvgCaseTI.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:29.267626+00:00
-- url     : https://prove2.me/theorems/35757bab-fc66-48a1-9b2c-e00869cb2016
-- title:
--   Theorem 6.5 — $\Pr[\mathrm{Tr}(A^2)=0]\to1/q$ with error $(q-1)q^{-n^2/2-1}$
-- statement:
--   Let $\mathbb F_q$ be a finite field and $\sigma(n,q)$ the probability that a uniform $A\in\mathrm M(n,q)$ is self-dual, $\mathrm{Tr}(A^2)=0$. Then
--   $$
--   \sigma(\infty,q):=\lim_{n\to\infty}\sigma(n,q)=\frac1q,
--   $$
--   and for every $n\ge0$,
--   $$
--   |\sigma(\infty,q)-\sigma(n,q)|\le\Sigma(n,q):=(q-1)\,q^{-\frac{n^2}{2}-1}.
--   $$
--
--   This is the denominator of the conditional probabilities of Theorems 3.5 and 6.11, and it counts the self-dual lines used in the proof of Proposition 3.6.
--
--   **Formalization Note** The exponent $-n^2/2-1$ is a real power. Both odd and even characteristic are covered.
--
--   Differences from the source:
--
--   - encoding: a statement "lim x(n) = L" → `Tendsto x atTop (𝓝 L)` → same statement; reason: Lean convention
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.5, Eq. (42), p.38 (PDF p.40)

import Mathlib
import Definitions.Def_AvgCaseTI_selfDualProb

set_option autoImplicit false

namespace AvgCaseTI

open Filter Topology

/-- **Theorem 6.5 (probability that a uniform matrix is self-dual).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.5, p.38
(PDF p.40): for every finite field with `q` elements, `σ(n, q) = Pr[Tr(A²) = 0]` satisfies
`σ(∞, q) := lim σ(n, q) = 1/q` and, for every `n`,
`|σ(∞, q) − σ(n, q)| ≤ Σ(n, q) := (q − 1)·q^{−n²/2 − 1}`.

**Formalization Note.** `q^{−n²/2 − 1}` is a real power. Both parities of `q` are covered. -/
theorem theorem_6_5 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    Tendsto (selfDualProb K) atTop (𝓝 (1 / (q : ℝ))) ∧
    ∀ n : ℕ, |1 / (q : ℝ) - selfDualProb K n| ≤
      ((q : ℝ) - 1) * (q : ℝ) ^ (-(n : ℝ) ^ 2 / 2 - 1) := by sorry

end AvgCaseTI
