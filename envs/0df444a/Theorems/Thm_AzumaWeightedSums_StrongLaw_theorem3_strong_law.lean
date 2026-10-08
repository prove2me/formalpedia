-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_theorem3_strong_law
-- name    : AzumaWeightedSums.StrongLaw.theorem3_strong_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:35.097475+00:00
-- url     : https://prove2.me/theorems/0bb8376a-7917-49b1-8127-4e8aa0532ccc
-- title:
--   Theorem 3 — $\bar S_n/A_n \to 0$ a.s. for bounded martingale differences under $a_n/A_n = o(1/\log\log A_n)$
-- statement:
--   Let $(\Omega,\mathfrak A,P)$ be a probability space with an increasing family $(\mathfrak A_n)$ of sub-$\sigma$-fields, and let $(x_n)_{n\ge1}$ be a sequence of martingale differences with respect to $(\mathfrak A_n)$ such that $|x_n|\le1$ almost surely for every $n$. Let $(a_n)_{n\ge1}$ be a sequence of positive nondecreasing numbers, put $A_n = a_1+\dots+a_n$ and form the reversed weighted sums $\bar S_n = a_nx_1 + a_{n-1}x_2+\dots+a_1x_n$. If
--
--   $$\frac{a_n}{A_n} = o\Big(\frac{1}{\log\log A_n}\Big)\quad\text{as } n\to\infty, \tag{4.9}$$
--
--   then
--
--   $$\frac{\bar S_n}{A_n} \longrightarrow 0 \quad\text{as } n\to\infty,\ \text{almost surely}. \tag{4.10}$$
--
--   This is a strong law of large numbers for weighted averages in which the weights are applied in reverse order, so that $(\bar S_n)$ is not a martingale. The growth condition (4.9) is weaker than the condition $a_n^2/D_n^2\to0$ of Theorem 2, where $D_n^2=\sum_{j\le n}a_j^2$.
--
--   **Formalization Note** "Positive increasing" is read as $a_n>0$ and $a_n\le a_{n+1}$ for $n\ge1$ (nondecreasing), the weaker hypothesis, which is all the proof uses. Indices start at $1$; $a_0$ and $x_0$ are unused. Condition (4.9) is stated literally as a little-$o$ relation along $n\to\infty$; $A_n\to\infty$ is not assumed, since it follows from $a_n\ge a_1>0$. The conclusion is ordinary convergence of a real sequence to $0$ for almost every $\omega$, which covers both tails.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 364, Theorem 3, (4.9)–(4.10)

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace AzumaWeightedSums.StrongLaw

open MeasureTheory Filter Asymptotics Topology

/-- Theorem 3 (Azuma 1967, p. 364). Let `(x_n)` be a sequence of martingale differences such that
`|x_n| ≤ 1` a.s. and `(a_n)` a sequence of positive increasing numbers. If
(4.9) `a_n/A_n = o(1/log log A_n)` as `n → ∞`, then (4.10) `S̄_n/A_n → 0` as `n → ∞`, a.s. -/
theorem theorem3_strong_law {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n)))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Sbar a x n ω / A a n) atTop (𝓝 0) := by sorry

end AzumaWeightedSums.StrongLaw
