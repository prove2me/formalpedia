-- Prove2me | Theorems.Thm_AvgCaseTI_Supplement_theorem_6_3
-- name    : AvgCaseTI.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:37:33.889653+00:00
-- url     : https://prove2.me/theorems/51a5640d-9211-4b70-b782-a259eeddaa9e
-- title:
--   Theorem 6.3 — matrices with a unique simple $\mathbb F_q$-eigenvalue: limit $q\,c(q)^q/(q-1)\ge e^{-23/9}$ and rate
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements and $\alpha(n,q)=|C_1(n,q)|/|\mathrm M(n,q)|$ the probability that a uniform $A\in\mathrm M(n,q)$ has exactly one eigenvalue in $\mathbb F_q$, of algebraic multiplicity $1$. Then
--
--   1. the limit exists and
--   $$
--   \alpha(\infty,q):=\lim_{n\to\infty}\alpha(n,q)=\frac{q\cdot c(q)^q}{q-1};
--   $$
--   2. $\alpha(\infty,q)\ge e^{-23/9}$;
--   3. for every $n>5(q-1)^2$,
--   $$
--   |\alpha(\infty,q)-\alpha(n+1,q)|\le\frac{q}{q-1}\left(\frac12\,16^{q-1}q^{-(n+1)(n+q)/(2(q-1))}+4q^{-(n+1)}\right).
--   $$
--
--   A random matrix over $\mathbb F_q$ therefore has a unique simple $\mathbb F_q$-eigenvalue with probability bounded below by an absolute constant, with an explicit superexponential-plus-exponential rate.
--
--   Differences from the source:
--
--   - encoding: lim_{n→∞} α(n, q) and c(q) → Tendsto (alphaOne K) atTop (𝓝 (q·c(q)^q/(q−1))), c(q) = cInf q, K any finite field with q elements; reason: limits as Tendsto (reading R8); the third clause bounds the distance from that same value
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.3, Eq. (39), p.37 (PDF p.39)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_Supplement_alphaOne

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI Filter Topology

/-- **Theorem 6.3 (matrices with a unique simple `F_q`-eigenvalue).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.3, p.37 (PDF p.39): "Let α(n, q) := |C₁(n,q)| / |M(n,q)| be the probability of a random
matrix A ∈ M(n, q) which has only 1 eigenvalue in F_q with algebraic multiplicity 1. Then we have
α(∞, q) := lim_{n→∞} α(n, q) = q · c(q)^q / (q − 1) ≥ e^{−23/9}. Moreover, for any n > 5(q − 1)², we have:
|α(∞, q) − α(n + 1, q)| ≤ q/(q − 1) · (½ 16^{q−1} q^{−(n+1)(n+q)/(2(q−1))} + 4q^{−(n+1)}). (39)"

For every finite field `K` with `q` elements:
1. `α(n, q) → q · c(q)^q / (q − 1)`;
2. `q · c(q)^q / (q − 1) ≥ e^{−23/9}`;
3. for every `n > 5(q − 1)²`,
   `|q c(q)^q/(q − 1) − α(n + 1, q)| ≤ q/(q − 1) · (½·16^{q−1}·q^{−(n+1)(n+q)/(2(q−1))} + 4 q^{−(n+1)})`.

**Formalization Note.** `c(q) = cInf q`; the exponent `−(n+1)(n+q)/(2(q−1))` is a real power. -/
theorem theorem_6_3 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    Tendsto (alphaOne K) atTop (𝓝 ((q : ℝ) * cInf q ^ q / ((q : ℝ) - 1))) ∧
    Real.exp (-(23 / 9)) ≤ (q : ℝ) * cInf q ^ q / ((q : ℝ) - 1) ∧
    ∀ n : ℕ, 5 * (q - 1) ^ 2 < n →
      |(q : ℝ) * cInf q ^ q / ((q : ℝ) - 1) - alphaOne K (n + 1)| ≤
        (q : ℝ) / ((q : ℝ) - 1) *
          (1 / 2 * (16 : ℝ) ^ (q - 1) *
              (q : ℝ) ^ (-(((n : ℝ) + 1) * ((n : ℝ) + q)) / (2 * ((q : ℝ) - 1))) +
            4 * (q : ℝ) ^ (-((n : ℤ) + 1))) := by sorry

end AvgCaseTI.Supplement
