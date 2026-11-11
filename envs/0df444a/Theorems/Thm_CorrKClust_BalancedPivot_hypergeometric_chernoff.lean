-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_hypergeometric_chernoff
-- name    : CorrKClust.BalancedPivot.hypergeometric_chernoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:39.424195+00:00
-- url     : https://prove2.me/theorems/f08c3b92-4940-4736-a0d1-17f93ce48323
-- title:
--   Facts 2.1–2.2 — Chernoff bounds for independent or negatively associated sums, and hypergeometric counts
-- statement:
--   **Part 1 (Fact 2.1).** Let $X_1,\dots,X_m$ be $\{0,1\}$-valued random variables that are mutually independent or negatively associated, let $X=\sum_{i=1}^m X_i$ and $\mu=\mathbb E[X]$. Then
--   $$\Pr[X\ge(1+\delta)\mu]\le e^{-\delta^2\mu/(2+\delta)}\ (\delta>0),\qquad\Pr[X\le(1-\delta)\mu]\le e^{-\delta^2\mu/2}\ (0<\delta<1),$$
--   $$\Pr[X\ge a]\le2^{-a}\ (a\ge2e\mu),\qquad\Pr[X\ge(1+\delta)\mu]\le e^{-\delta\mu/3}\ (\delta\ge1).$$
--
--   **Part 2 (Fact 2.2).** Let $A$ be a set of $K$ marked elements of a population $V$ of size $n>0$, and let $0\le t\le n$. Draw a uniform permutation of $V$ and let $X$ count the marked elements among its first $t$ positions, so $X\sim\mathrm{Hypergeometric}(n,K,t)$. Then $\mathbb E[X]=Kt/n$; $X=\sum_{i<t}Y_i$, where $Y_i$ indicates that position $i$ holds a marked element; the $Y_i$ are negatively associated and each equals $1$ with probability $K/n$; and the four tail bounds of Part 1 hold for $X$.
--
--   These are the concentration tools of §7: Lemmas 7.5, 7.7, 7.8 and 7.9 apply them to hypergeometric counts.
--
--   Differences from the source:
--   - encoding: random variables on an arbitrary probability space → explicit nonnegative probability weights summing to 1 on a finite sample space Ω : Type; reason: every probability in Fact 2.1 depends only on the joint law of (X_1,…,X_m) on the finite set {0,1}^m, and every such law is a weighted finite space; negative association is the Joag-Dev–Proschan covariance condition for coordinatewise nondecreasing functions of disjoint coordinate sets
--   - encoding: uniform random arrival order → uniform weights 1/|Fin (card V) ≃ V| on all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: a sample of size t drawn without replacement from a population of size n → a fixed marked subset and the first t positions of a uniform permutation, with n > 0 and t ≤ n; reason: this realizes exactly the hypergeometric law; n = 0 forces t = 0 and the empty sample
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Facts 2.1–2.2, p. 11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Facts 2.1--2.2, p. 11. Part 1 (Fact 2.1): every sum of independent or negatively associated
`{0,1}`-valued variables satisfies the four tail bounds. Part 2 (Fact 2.2): for a hypergeometric
count, realized as the number of marked elements among the first `t` positions of a uniform
permutation, `E[X] = Kt/n`, `X` is the sum of `t` negatively associated `{0,1}` indicators each
equal to `1` with probability `K/n`, and the four tail bounds hold for `X`. -/
theorem hypergeometric_chernoff :
    (∀ (Ω : Type) [Fintype Ω] (p : Ω → ℝ), IsProbWeights p →
      ∀ (m : ℕ) (X : Fin m → Ω → ℝ), (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
      (MutuallyIndependent p X ∨ NegativelyAssociated p X) →
      ChernoffTails p (fun ω => ∑ i, X i ω)) ∧
    (∀ (V : Type) [Fintype V] (hn : 0 < Fintype.card V) (A : Finset V) (t : ℕ)
      (ht : t ≤ Fintype.card V),
      let u : ArrivalOrder V → ℝ := fun _ => 1 / (Fintype.card (ArrivalOrder V) : ℝ)
      let X : ArrivalOrder V → ℝ := fun σ => (prefixCount A t σ : ℝ)
      let Y : Fin t → ArrivalOrder V → ℝ :=
        fun i σ => if σ (Fin.castLE ht i) ∈ A then 1 else 0
      wExp u X = (A.card : ℝ) * t / Fintype.card V ∧
      (∀ σ, X σ = ∑ i, Y i σ) ∧
      (∀ i, wProb u (fun σ => Y i σ = 1) = (A.card : ℝ) / Fintype.card V) ∧
      NegativelyAssociated u Y ∧
      ChernoffTails u X) := by sorry

end CorrKClust.BalancedPivot
