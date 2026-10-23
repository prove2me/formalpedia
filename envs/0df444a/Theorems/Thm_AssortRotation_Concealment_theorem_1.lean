-- Prove2me | Theorems.Thm_AssortRotation_Concealment_theorem_1
-- name    : AssortRotation.Concealment.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:20.573978+00:00
-- url     : https://prove2.me/theorems/9ea0a702-276a-4cde-9542-e5713dd2dd2e
-- title:
--   Theorem 1, p. 15 — decreasing-price sequential revenue ≥ $R^f_*$ pathwise, and $\mathbb E[R^s_*]\ge\mathbb E[R^f_*]$
-- statement:
--   A retailer has $N$ products with nonnegative prices $p_1,\dots,p_N$. Its consumer has realized valuation shocks $X_1,\dots,X_N$, which are mutually independent, continuous, integrable random variables on a probability space $(\Omega,\mathbb P)$, and a nonnegative, decreasing marginal utility $v$. Let $R^f(S)$ be the fixed-assortment revenue (4) of a subset $S$ of products. Let $\mathbb E[R^f_*]=\max_S\mathbb E[R^f(S)]$ over all subsets, and $\mathbb E[R^s_*]$ the largest expected sequential revenue over all orders of all $N$ products.
--
--   1. **(a)** Suppose that $S$ is an optimized fixed assortment, $\mathbb E[R^f(S)]=\mathbb E[R^f_*]$, with $M\le N$ products. Let $R$ be the revenue of the sequential assortment that offers the same $M$ products in decreasing order of prices, $p_1\ge\cdots\ge p_M$. Then for every outcome $\omega$
--   $$
--   R(\omega)\ \ge\ R^f_*(\omega).
--   $$
--   2. **(b)** The retailer's value of concealment is (weakly) positive:
--   $$
--   \mathbb E[R^s_*]\ \ge\ \mathbb E[R^f_*].
--   $$
--
--   This is the paper's central result. Concealing products and revealing them one at a time is never worse for the retailer than a fixed assortment. The decreasing-price sequence of the optimal fixed assortment already earns at least as much.
--
--   **Formalization Note.** "With probability 1" in (a) is strengthened to every outcome $\omega$. Any order among equal prices is allowed in (a). Prices are assumed nonnegative, which is implicit in the paper. Independence, continuity (null singletons for the law of each $X_i$), integrability and measurability are the paper's standing assumptions (§2(d) and Notation, p. 10). They are kept even though the inequality does not use them. $R^f_*(\omega)$ is computed with the canonical Definition-1 order (ties broken by index), and other orders differ only on a null tie event. "Positive" is meant in the weak sense, the paper's convention (p. 10).
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 15, Theorem 1 (proof p. 39); VoC definition p. 12

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

open MeasureTheory ProbabilityTheory

/-- Theorem 1, p. 15. In the model of §2 (`N` products with nonnegative prices `p`,
independent, continuous, integrable valuation shocks `X`, marginal utility `v`):
(a) if `S` is an optimized fixed assortment, then for every outcome `ω` the sequential
revenue `R` of the same products shown in decreasing order of prices (any order among equal
prices) is at least `R^f_*(ω)`;
(b) the value of concealment is (weakly) positive: `E[R^f_*] ≤ E[R^s_*]`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (v : ℕ → ℝ) (hv : MarginalUtility v) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (hind : iIndepFun X μ) (hcont : ∀ i, NullSingletonClass (μ.map (X i))) :
    (∀ S : Finset (Fin N), (∫ ω, RfSet v p X S ω ∂μ = ERfStar μ v p X) →
      ∀ ω : Ω, ∀ L : List (ℝ × ℝ), L.Perm (products p X S ω) →
        L.Pairwise (fun a b => b.1 ≤ a.1) → RfSet v p X S ω ≤ seqRev v L 0) ∧
    ERfStar μ v p X ≤ ERsStar μ v p X := by sorry

end AssortRotation.Concealment
