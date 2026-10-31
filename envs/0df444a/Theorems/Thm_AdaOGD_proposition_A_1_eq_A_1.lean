-- Prove2me | Theorems.Thm_AdaOGD_proposition_A_1_eq_A_1
-- name    : AdaOGD.proposition_A_1_eq_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:32.242982+00:00
-- url     : https://prove2.me/theorems/8e16b4e6-5755-47dc-9555-b76302f270ec
-- title:
--   Proposition A.1, (A.1) (corrected: $(1-p_0)^{-x}$ for $e^{xp_0}$) — $\sum_n\mathbb P(\bar X_n\le x)\le(1-p_0)^{-x}$
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. Geometric($p_0$) random variables on $\{1,2,\dots\}$ with $p_0\in(0,1)$, and let $\bar X_n=\max_{1\le i\le n}X_i$. Then for every real $x$,
--   $$
--   \sum_{n=1}^{+\infty}\mathbb P(\bar X_n\le x)\ \le\ (1-p_0)^{-x}.
--   $$
--
--   The bound controls how long the running maximum of the draws can stay small, which is how the paper turns the random step sizes into an expectation bound.
--
--   **Formalization Note** The series has nonnegative terms and is stated through all its partial sums: $\sum_{n=1}^{n_0}\mathbb P(\bar X_n\le x)\le(1-p_0)^{-x}$ for every $n_0$. The variables are one i.i.d. sequence `X 0, X 1, …`, and $\bar X_n$ is the maximum of the first $n$.
--
--   Differences from the source:
--   - correction: $\sum_{n\ge1}\mathbb P(\bar X_n\le x)\le e^{xp_0}$ → $\le(1-p_0)^{-x}$; reason: the printed bound is false: for $p_0=0.9$, $x=2$ the sum is $(1-0.01)/0.01=99>e^{1.8}\approx6.05$; the proof derives $(1-p_0)^{-x}$ and then applies $1-p_0\le e^{-p_0}$ in the wrong direction
--   - generalization: $x$ unquantified in the statement; the proof fixes $x\ge1$ (p.36) → every real $x$; reason: for $x<1$ every term of the series is $0$ and the bound is positive; the case $x\ge1$ is the source
--   - encoding: $X_1,\dots,X_n$ i.i.d. for each $n$, and the infinite series → one i.i.d. sequence, and every partial sum of the series; reason: $\mathbb P(\bar X_n\le x)$ depends only on the common law; a series of nonnegative terms is bounded iff all partial sums are
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, Appendix A, Proposition A.1, display (A.1), p.36 (the corrected bound is the proof's "≤ 1/q0^x = (1 − p0)^−x", p.36)

import Mathlib
import Definitions.Def_AdaOGD_eta

namespace AdaOGD

open MeasureTheory ProbabilityTheory

/-- Proposition A.1, (A.1), corrected (Jordan, Lin & Zhou, arXiv:2310.14085v4, Appendix A, p.36):
let `X₁, X₂, …` be i.i.d. Geometric(`p₀`) on `{1, 2, …}` with `p₀ ∈ (0, 1)` and
`X̄ₙ = max_{1≤i≤n} Xᵢ`. Then for every real `x`, `∑_{n=1}^{∞} ℙ(X̄ₙ ≤ x) ≤ (1 − p₀)^{−x}`.

**Formalization Note** The printed right-hand side `e^{x p₀}` is false (`p₀ = 0.9`, `x = 2`: the sum
is `99 > e^{1.8}`); the bound stated is `(1 − p₀)^{−x}`, the one the printed proof derives. The
proof fixes `x ≥ 1`; for `x < 1` every term of the series is `0`, so the bound holds for every real
`x`. The variables are one i.i.d. sequence `X 0, X 1, …` and `X̄ₙ` is the maximum of the first `n`. The
series of nonnegative terms is stated through all its partial sums. -/
theorem proposition_A_1_eq_A_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1) (X : ℕ → Ω → ℕ)
    (hind : iIndepFun X P) (hgeom : ∀ n, IsGeometric P p₀ (X n)) (x : ℝ) (n₀ : ℕ) :
    ∑ n ∈ Finset.Icc 1 n₀, P.real {ω | (((Finset.range n).sup fun k => X k ω : ℕ) : ℝ) ≤ x}
      ≤ (1 - p₀) ^ (-x) := by sorry

end AdaOGD
