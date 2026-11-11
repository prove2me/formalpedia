-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_3_5
-- name    : DynColorWC.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:06.419826+00:00
-- url     : https://prove2.me/theorems/a3492929-c576-4e1a-9491-93080406b971
-- title:
--   Lemma 3.5 — sequentially p-dominated 0/1 sums are dominated by Bin(n,p) and obey its Chernoff upper tail
-- statement:
--   Let $X_1,\dots,X_n\in\{0,1\}$ be random variables such that for each $i$ and each setting of $X_1,\dots,X_{i-1}$, $\Pr[X_i=1\mid X_1,\dots,X_{i-1}]\le p$, and let $X=\sum_iX_i$. Then
--   1. $X$ is stochastically dominated by $\mathrm{Bin}(n,p)$: $\Pr[X\ge x]\le\Pr[\mathrm{Bin}(n,p)\ge x]$ for every $x$;
--   2. for every $\delta>0$, $\Pr[X\ge(1+\delta)np]\le\exp\big(-\delta^2np/(2(1+\delta))\big)$ (the Chernoff upper tail of Lemma 3.4 for the mean $np$ of $\mathrm{Bin}(n,p)$);
--   3. in particular, $\Pr[X\ge2np]\le\exp(-np/4)$.
--
--   Differences from the source:
--
--   - reading: X 'obeys the Chernoff upper tail stated in Lemma 3.4', i.e. with E[X] → with np: P[X ≥ (1+δ)np] ≤ exp(−δ²np/(2(1+δ))) for every δ > 0; reason: the literal E[X] reading is false (INSIGHTS I1: n = 201, p = 1/10, δ = 4 gives 0.0996 > 0.0347); np is the mean of the dominating Bin(n, p) and the mean the 'in particular' clause uses
--   - encoding: Pr[X_i = 1 | X_1, …, X_{i−1}] ≤ p for each setting of X_1, …, X_{i−1} → P[X_j = x_j ∀ j < i, X_i = 1] ≤ p·P[X_j = x_j ∀ j < i] for every i and every x; reason: equivalent for settings of positive probability; settings of probability 0 have no conditional probability and impose nothing
--   - encoding: X is stochastically dominated by Bin(n, p) → P[X ≥ x] ≤ Σ_{j ∈ {0..n}, j ≥ x} C(n,j) p^j (1−p)^{n−j} for every real x; reason: the definition of stochastic domination, with the binomial tail written out
--   - encoding: p (a bound on probabilities) → 0 ≤ p ≤ 1; reason: Bin(n, p) is defined only for p ∈ [0,1]; for p < 0 the hypothesis cannot hold
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 3.5, p. 14 (PDF 16)

import Mathlib

namespace DynColorWC.Main

open MeasureTheory

/-- **Lemma 3.5** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 14 (PDF 16)), with its Chernoff clause read with the mean `np` of `Bin(n, p)`.
Let `X_1, …, X_n ∈ {0, 1}` be random variables such that for each `i` and each setting
`x_1, …, x_{i−1}` of `X_1, …, X_{i−1}`, `Pr[X_i = 1 | X_1 = x_1, …, X_{i−1} = x_{i−1}] ≤ p`
(stated as `P[prefix ∧ X_i = 1] ≤ p · P[prefix]`, which is the conditional bound for every prefix of
positive probability). Let `X = Σ_i X_i`. Then
1. `X` is stochastically dominated by `Bin(n, p)`: `P[X ≥ x] ≤ Σ_{j ≥ x} C(n,j) p^j (1−p)^{n−j}` for
   every real `x`;
2. for all `δ > 0`, `P[X ≥ (1 + δ) np] ≤ exp(−δ² np / (2(1 + δ)))`;
3. in particular, `P[X ≥ 2np] ≤ exp(−np/4)`. -/
theorem lemma_3_5 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcond : ∀ (i : Fin n) (x : Fin n → ℝ),
      μ.real ({ω | ∀ j : Fin n, j < i → X j ω = x j} ∩ {ω | X i ω = 1}) ≤
        p * μ.real {ω | ∀ j : Fin n, j < i → X j ω = x j}) :
    (∀ x : ℝ, μ.real {ω | x ≤ ∑ i, X i ω} ≤
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => x ≤ (j : ℝ)),
        (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)) ∧
    (∀ δ : ℝ, 0 < δ →
      μ.real {ω | (1 + δ) * (n * p) ≤ ∑ i, X i ω} ≤
        Real.exp (-(δ ^ 2 * (n * p)) / (2 * (1 + δ)))) ∧
    μ.real {ω | 2 * (n * p) ≤ ∑ i, X i ω} ≤ Real.exp (-(n * p) / 4) := by sorry

end DynColorWC.Main
