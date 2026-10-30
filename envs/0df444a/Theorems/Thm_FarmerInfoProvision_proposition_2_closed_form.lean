-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_closed_form
-- name    : FarmerInfoProvision.proposition_2_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:33.736101+00:00
-- url     : https://prove2.me/theorems/6f2cfe99-b59f-4a77-9f60-6483950416b1
-- title:
--   Proposition 2 on the closed-form welfare: $n_1^*$ maximizes $n_1W^I+(n-n_1)W^J$ over $n_1\in\{0,\dots,n\}$
-- statement:
--   Let $W(n_1,\beta;\gamma)=n_1W^I(n_1,\beta;\gamma)+(n-n_1)W^J(n_1,\beta;\gamma)$ with Lemma 2's closed forms, $V(n,\beta;\gamma)$ the provision index, and
--
--   $$
--   n_1^*=\begin{cases}1&\text{if }V(n,\beta;\gamma)>0,\\0&\text{if }V(n,\beta;\gamma)\le0.\end{cases}
--   $$
--
--   For $n\ge4$, $a,b,\alpha,\beta>0$ and $\gamma\ge0$:
--
--   1. $W(m,\beta;\gamma)\le W(n_1^*,\beta;\gamma)$ for every integer $0\le m\le n$;
--   2. $W(m,\beta;\gamma)<W(n_1^*,\beta;\gamma)$ for every integer $0\le m\le n$ with $m\ne n_1^*$ and either $m\ge2$ or $V(n,\beta;\gamma)\ne0$.
--
--   This is the central planner's problem (5) solved on Lemma 2's formulas; with Propositions 1 and Lemma 2 it gives Proposition 2 for the game.
--
--   Differences from the source:
--   - reading: n1 ∈ [0, n] in problem (5) → integers m with 0 ≤ m ≤ n; reason: n1 = |I| is a number of farmers (pp. 9, 11) and the proof compares the integers 0, 1, 2; over the real interval the statement is false (n = 4, α = β = γ = 1: W(0.525) > W(1) > W(0))
--   - reading: the optimal information provision policy n1* satisfies n1* = 1 if V > 0, 0 if V ≤ 0 → n1* is a maximizer, and every other m is strictly worse when m ≥ 2 or V ≠ 0; reason: 'the optimal' asserts uniqueness, which holds except at V = 0, where the policies 0 and 1 tie and the paper picks 0
--   - encoding: the closed forms contain 1/γ, undefined at γ = 0 → Lean's 1/0 = 0, multiplied by A1² = B1² = 0; reason: at γ = 0 the formulas take their γ → 0 limits, so γ = 0 (no private signal) is covered with its intended values
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14, with problem (5), p. 11 (proof pp. 35–36)

import Mathlib
import Definitions.Def_FarmerInfoProvision_totalWelfare
import Definitions.Def_FarmerInfoProvision_provisionIndex
import Definitions.Def_FarmerInfoProvision_optimalCount

namespace FarmerInfoProvision

/-- **Proposition 2 on the closed-form welfare: `n1*` maximizes `n1 W^I + (n − n1) W^J` over
`n1 ∈ {0, …, n}`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, p. 14: "By applying Lemma 2, we can determine the farmers'
total (ex ante) expected profit `W(n1, β; γ) ≡ {n1 W^I(n1, β; γ) + (n − n1) W^J(n1, β; γ)}`. By
considering `W(n1, β; γ)` along with (5), we get: Proposition 2. The optimal information
provision policy `n1*` satisfies: `n1* = 1` if `V(n, β; γ) > 0`; `0` if `V(n, β; γ) ≤ 0`"; (5),
p. 11: "`S* = max_{n1 ∈ [0,n]} W(n1, β; γ)`".

For `n ≥ 4` farmers, `b, α, β > 0` and `γ ≥ 0`, with `n1* = optimalCount n α β γ`:
1. `W(m) ≤ W(n1*)` for every integer `0 ≤ m ≤ n`;
2. `W(m) < W(n1*)` for every integer `0 ≤ m ≤ n` with `m ≠ n1*` and either `m ≥ 2` or
   `V(n, β; γ) ≠ 0`.

**Formalization Note.** `n1` ranges over the numbers of informed farmers `0, …, n`: `n1 = |I|`
(p. 9) and the proof compares integers. Over the real interval `[0, n]` the statement is false
(e.g. `n = 4`, `α = β = γ = 1`: `W(0.525) > W(1)`). Clause 2 is what "the optimal policy"
asserts beyond "an optimal policy"; at `V = 0` the policies `0` and `1` tie. -/
theorem proposition_2_closed_form {n : ℕ} (hn : 4 ≤ n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∀ m : ℕ, m ≤ n →
      totalWelfare a b c (n : ℝ) (m : ℝ) α β γ ≤
        totalWelfare a b c (n : ℝ) (optimalCount (n : ℝ) α β γ : ℝ) α β γ) ∧
    (∀ m : ℕ, m ≤ n → m ≠ optimalCount (n : ℝ) α β γ →
      (2 ≤ m ∨ provisionIndex (n : ℝ) α β γ ≠ 0) →
      totalWelfare a b c (n : ℝ) (m : ℝ) α β γ <
        totalWelfare a b c (n : ℝ) (optimalCount (n : ℝ) α β γ : ℝ) α β γ) := by sorry

end FarmerInfoProvision
