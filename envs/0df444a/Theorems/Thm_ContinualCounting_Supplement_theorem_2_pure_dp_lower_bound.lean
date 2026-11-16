-- Prove2me | Theorems.Thm_ContinualCounting_Supplement_theorem_2_pure_dp_lower_bound
-- name    : ContinualCounting.Supplement.theorem_2_pure_dp_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:00:20.867684+00:00
-- url     : https://prove2.me/theorems/ff45911e-09e9-4c3c-af9a-a3095a003c80
-- title:
--   Theorem 2 — every pure $\varepsilon$-DP mechanism for prefix sums has $\ell_\infty$ error $\Omega(\log^2 n/\varepsilon)$
-- statement:
--   Let $A$ be the $n\times n$ prefix-sum matrix, $(Ax)_i=\sum_{j\le i}x_j$. A mechanism $M$ assigns to every input $x\in\{0,1\}^n$ a probability law $M(x)$ on $\mathbb R^n$; it is **$\varepsilon$-DP** (pure differential privacy, Definition 1 with $\delta=0$) if $\Pr[M(x)\in S]\le e^{\varepsilon}\Pr[M(x')\in S]$ for every measurable $S\subseteq\mathbb R^n$ and all inputs $x,x'$ that differ in exactly one coordinate.
--
--   For every $\kappa>0$ there are constants $c>0$ and $N$, depending only on $\kappa$, such that for all $n\ge N$, all $\varepsilon$ with $n^{-1+\kappa}<\varepsilon<1$, and every $\varepsilon$-DP mechanism $M$,
--   $$\max_{x\in\{0,1\}^n}\mathbb E\big[\|M(x)-Ax\|_\infty\big]\ge\frac{c\,\log^2 n}{\varepsilon}.$$
--
--   This matches the $O(\log^2(n)/\varepsilon)$ error of the Laplace binary tree mechanism, so the binary tree mechanism is optimal for continual counting under pure differential privacy. It is stronger than the approximate-DP bound $\Omega(\log^{3/2}n/\max\{\varepsilon,\delta\})$ of Theorem 1, which does not cover $\delta=0$.
--
--   **Formalization Note** Pure DP is the published predicate `ContinualCounting.IsDP M ε 0`; the error is the published `ContinualCounting.linfError M`, a supremum over inputs of a `lintegral` of the sup norm with values in $[0,\infty]$, so a non-integrable error counts as $\infty$. The logarithm is natural.
--
--   Differences from the source:
--   - reading: "For any n^{−1+Ω(1)} < ε < 1 … = Ω(log^2 n / ε)" → ∀ κ > 0, ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ ε ∈ (n^{−1+κ}, 1); reason: the standard meaning of the asymptotic statement: c and N depend only on κ (through m = n^{Ω(1)} in the proof, p.34), never on ε or M
--   - generalization: "any ε-DP mechanism M for continual counting" → every (offline) mechanism {0,1}^n → probability laws on ℝ^n; reason: online mechanisms are a special case, and the paper states the bound in the offline model (p.3)
--   - encoding: log, max over x, expectation of the sup norm → `Real.log` (natural), `⨆`, `lintegral` of `enorm` in ℝ≥0∞; reason: the base of the logarithm only moves c; the error may be ∞
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Theorem 2, p.2 (PDF p.3), restated §6, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_ContinualCounting_linfError

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting.Supplement

/-- **Theorem 2.** Bairaktari, Dahl, Larsen, *The Binary Tree Mechanism is Optimal for Differentially
Private Continual Counting*, arXiv:2607.00876 (sha256 986e6426…), p.2, restated §6, p.30: "For any
n^{−1+Ω(1)} < ε < 1, it holds that any ε-DP mechanism M for continual counting has error
max_{x∈{0,1}^n} E[∥M(x) − Ax∥∞] = Ω(log^2 n / ε), where A is the n × n prefix-sum matrix."

**Formalization Note.** Pure ε-DP is `IsDP M ε 0` (Definition 1, p.2: "The case where δ = 0 is
referred to as pure DP"). The asymptotics read: for each `κ > 0` (the `Ω(1)` of the exponent)
constants `c > 0`, `N` depending only on `κ`; and every `n ≥ N`, `n^{−1+κ} < ε < 1`. The mechanism is
arbitrary (data-dependent noise, the whole input visible, the offline model of p.3), which contains
the online ones. Mechanisms are probability laws on `ℝ^n`. The logarithm is natural. The error
`linfError M` is `max_x E‖M(x) − Ax‖∞` in `ℝ≥0∞`. -/
theorem theorem_2_pure_dp_lower_bound :
    ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ ε : ℝ, (n : ℝ) ^ (-1 + κ) < ε → ε < 1 →
      ∀ M : (Fin n → Bool) → Measure (Fin n → ℝ), (∀ x, IsProbabilityMeasure (M x)) →
        IsDP M ε 0 →
        ENNReal.ofReal (c * Real.log n ^ 2 / ε) ≤ linfError M := by sorry

end ContinualCounting.Supplement
