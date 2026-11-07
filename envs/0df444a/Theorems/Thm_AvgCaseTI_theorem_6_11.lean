-- Prove2me | Theorems.Thm_AvgCaseTI_theorem_6_11
-- name    : AvgCaseTI.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:43.623823+00:00
-- url     : https://prove2.me/theorems/834be064-694d-4220-9c8d-38eac56e9dab
-- title:
--   Theorem 6.11 — a uniform self-dual matrix has a unique simple $\mathbb F_q$-eigenvalue with probability $\to q\,c(q)^q/(q-1)$
-- statement:
--   Let $\mathbb F_q$ be a finite field and $A$ uniform in $\mathrm M(n,q)$ conditioned on $\mathrm{Tr}(A^2)=0$. Let $\gamma(n,q)$ be the probability that $A$ has exactly one eigenvalue in $\mathbb F_q$, of algebraic multiplicity 1, and $\gamma^*(n,q)$ the probability of the same event with the eigenvalue nonzero. Then
--   1. $\displaystyle \gamma(\infty,q):=\lim_{n\to\infty}\gamma(n,q)=\frac{q\,c(q)^q}{q-1}>e^{-23/9}$;
--   2. $\displaystyle \lim_{n\to\infty}\gamma^*(n,q)=c(q)^q\ge e^{-23/9}$;
--   3. for $n-1>5(q-1)^2$,
--   $$
--   |\gamma(\infty,q)-\gamma(n,q)|\le\frac{q^2}{1-(q-1)q^{-n^2/2}}\Bigl((q-1)q^{-\frac{n^2}{2}-1}+\frac{q}{q-1}\bigl(q^{-(n+1)}+\Gamma(n-1,q)\bigr)\Bigr),
--   $$
--   with $\Gamma$ the error term of Theorem 6.12.
--
--   This is the paper's main random-matrix estimate: it shows that the hull generator in the algorithm of Theorem 1.1 has the required spectrum with constant probability.
--
--   **Formalization Note** Non-integer exponents are real powers; $n-1$ is natural-number subtraction, exact because the hypothesis forces $n\ge7$.
--
--   Differences from the source:
--
--   - encoding: a statement "lim x(n) = L" → `Tendsto x atTop (𝓝 L)` → same statement; reason: Lean convention
--   - encoding: c(q) = lim c_n(q) (an infinite product) → `cInf q`, the infimum of the decreasing positive partial products → same value; reason: Lean convention
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.11, Eq. (51), p.42 (PDF p.44)

import Mathlib
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_betaProb
import Definitions.Def_AvgCaseTI_gammaProb

set_option autoImplicit false

namespace AvgCaseTI

open Filter Topology

/-- **Theorem 6.11 (unique simple `F_q`-eigenvalue of a uniform self-dual matrix).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.11, p.42
(PDF p.44). For every finite field with `q` elements:
1. `γ(n, q) → γ(∞, q) = q·c(q)^q/(q − 1) > e^{−23/9}`;
2. `γ*(n, q) → c(q)^q ≥ e^{−23/9}` (Eq. (51));
3. for `n − 1 > 5(q − 1)²`,
   `|γ(∞, q) − γ(n, q)| ≤ q²/(1 − (q−1)q^{−n²/2}) · ((q−1)q^{−n²/2−1} + q/(q−1)·(q^{−(n+1)} + Γ(n−1, q)))`.

**Formalization Note.** `γ`, `γ*` are ratios of counts over the self-dual matrices (`gammaProb`,
`gammaStarProb`); `Γ` is `GammaBound`; non-integer exponents are real powers. -/
theorem theorem_6_11 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q) :
    Tendsto (gammaProb K) atTop (𝓝 ((q : ℝ) * cInf q ^ q / ((q : ℝ) - 1))) ∧
    Real.exp (-(23 / 9)) < (q : ℝ) * cInf q ^ q / ((q : ℝ) - 1) ∧
    Tendsto (gammaStarProb K) atTop (𝓝 (cInf q ^ q)) ∧
    Real.exp (-(23 / 9)) ≤ cInf q ^ q ∧
    ∀ n : ℕ, 5 * (q - 1) ^ 2 < n - 1 →
      |(q : ℝ) * cInf q ^ q / ((q : ℝ) - 1) - gammaProb K n| ≤
        (q : ℝ) ^ 2 / (1 - ((q : ℝ) - 1) * (q : ℝ) ^ (-(n : ℝ) ^ 2 / 2)) *
          (((q : ℝ) - 1) * (q : ℝ) ^ (-(n : ℝ) ^ 2 / 2 - 1) +
            (q : ℝ) / ((q : ℝ) - 1) * ((q : ℝ) ^ (-((n : ℤ) + 1)) + GammaBound q (n - 1))) := by sorry

end AvgCaseTI
