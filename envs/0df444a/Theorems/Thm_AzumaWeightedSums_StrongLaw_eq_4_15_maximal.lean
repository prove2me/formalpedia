-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_eq_4_15_maximal
-- name    : AzumaWeightedSums.StrongLaw.eq_4_15_maximal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:32.469691+00:00
-- url     : https://prove2.me/theorems/b1982cee-421e-4dcc-8e2e-8ee8badf9926
-- title:
--   (4.15) — $2P\{\bar S_{n_{k+1}} > (\varepsilon/2)A_{n_k}\} \ge P\{\max_{n_k<n\le n_{k+1}} \bar S_n > \varepsilon A_{n_k}\}$
-- statement:
--   Let $(x_n)_{n\ge1}$ be a sequence of martingale differences with respect to an increasing family $(\mathfrak A_n)$ of sub-$\sigma$-fields of a probability space, with $|x_n|\le 1$ almost surely for every $n\ge1$. Let $(a_n)_{n\ge1}$ be positive and nondecreasing, $A_n=a_1+\dots+a_n$ and $\bar S_n = a_nx_1+\dots+a_1x_n$. Let $\varepsilon>0$ and let $1\le N_0<N_1$ be indices with
--
--   $$A_{N_1} \le (1+\varepsilon/3)\,A_{N_0}.$$
--
--   Then
--
--   $$2\,P\{\bar S_{N_1} > (\varepsilon/2)A_{N_0}\} \;\ge\; P\Big\{\max_{N_0<n\le N_1} \bar S_n > \varepsilon A_{N_0}\Big\}.$$
--
--   In the proof of Theorem 3 this is applied with $N_0=n_k$, $N_1=n_{k+1}$, where (4.14) supplies $A_{n_{k+1}}\le(1+\varepsilon/3)A_{n_k}$. It is a Lévy-type maximal inequality: since $(\bar S_n)$ is not a martingale, Doob's inequality is not available, and this inequality controls the maximum over a block by the value at the block's end.
--
--   **Formalization Note** The event $\{\max_{N_0<n\le N_1}\bar S_n > \varepsilon A_{N_0}\}$ is written as $\{\exists n,\ N_0<n\le N_1,\ \bar S_n>\varepsilon A_{N_0}\}$, which is the same event since the index range is finite and nonempty. Probabilities are real-valued.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 365, proof of Theorem 3, display (4.15) (proved on pp. 365–366)

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace AzumaWeightedSums.StrongLaw

open MeasureTheory

/-- Display (4.15) (Azuma 1967, proof of Theorem 3, p. 365), for two indices `N₀ < N₁` in the
role of `n_k < n_{k+1}`: if `(x_n)` are martingale differences with `|x_n| ≤ 1` a.s., `(a_n)` is
positive and nondecreasing, `ε > 0` and `A_{N₁} ≤ (1 + ε/3) A_{N₀}`, then
`2 P{S̄_{N₁} > (ε/2) A_{N₀}} ≥ P{max_{N₀ < n ≤ N₁} S̄_n > ε A_{N₀}}`. -/
theorem eq_4_15_maximal {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (N₀ N₁ : ℕ) (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁)
    (hA : A a N₁ ≤ (1 + ε / 3) * A a N₀) :
    μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ 2 * μ.real {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} := by sorry

end AzumaWeightedSums.StrongLaw
