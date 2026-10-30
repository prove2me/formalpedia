-- Prove2me | Theorems.Thm_FarmerInfoProvision_lemma_2_ex_ante_profits
-- name    : FarmerInfoProvision.lemma_2_ex_ante_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:22.019986+00:00
-- url     : https://prove2.me/theorems/dcc29f46-f713-4329-8cce-06de2e4b654d
-- title:
--   Lemma 2: ex-ante equilibrium profits of informed and uninformed farmers, and $W^I>W^J$ (corrected: quantities unrestricted in sign)
-- statement:
--   Consider the production game: $n$ farmers choose quantities $q_i$ at unit cost $c$ and sell at the price $P(Q)=a-bQ+u$, $Q=\sum_i q_i$, where $a,b>0$ and the demand shock is $u\sim N(0,1/\alpha)$. Farmer $i$ privately observes a signal of $u$ of precision $\gamma\ge 0$ ($\gamma=0$: no private signal), and the farmers in a set $I$ also observe the public signal $y=u+\epsilon_r$, $\epsilon_r\sim N(0,1/\beta)$, all noises independent. Assume $a,b,\alpha,\beta>0$, $\gamma\ge0$, and let $n_1=|I|$. Then:
--
--   1. in every Bayesian Nash equilibrium of the game with informed set $I$, every informed farmer $i\in I$ earns ex-ante expected profit
--   $$
--   W^I(n_1,\beta;\gamma)=b\Bigl\{A_0^2+A_1^2\Bigl(\frac1\alpha+\frac1\gamma\Bigr)+A_2^2\Bigl(\frac1\alpha+\frac1\beta\Bigr)+2A_1A_2\frac1\alpha\Bigr\},
--   $$
--   and every uninformed farmer $j\notin I$ earns
--   $$
--   W^J(n_1,\beta;\gamma)=b\Bigl\{B_0^2+B_1^2\Bigl(\frac1\alpha+\frac1\gamma\Bigr)\Bigr\};
--   $$
--   2. $W^I(n_1,\beta;\gamma)>W^J(n_1,\beta;\gamma)$.
--
--   Access to the public signal is a competitive advantage. These formulas turn the central planner's problem (5) into a problem about explicit rational functions of $n_1$.
--
--   **Formalization Note** The proof's display of $W^I-W^J$ (p. 35) lacks a factor $4$; only the sign, which is the lemma's claim, is stated.
--
--   Differences from the source:
--   - correction: problems (2)–(3) maximize over quantities q ≥ 0 → quantities are unrestricted real numbers; reason: the paper's equilibrium (6)–(7) is infeasible under q ≥ 0: at n = 4, n1 = |I| = 1, α = β = γ = 1, a = 2, b = c = 1 (all assumptions hold), A2 = 1/10 > 0 and y is a nondegenerate Gaussian, so q_i = A0 + A1x_i + A2y < 0 with positive probability; with q ≥ 0 imposed, W^I and W^J are not equilibrium profits. Footnote 6 (p. 8) treats negative prices and quantities as a negligible convention
--   - encoding: interim best responses: maximize the conditional expected profit given the farmer's own signals → ex-ante best responses over Borel functions of the same signals with square-integrable output; reason: equivalent for square-integrable strategies (the ex-ante profit is the conditional one integrated over the signals); square integrability is what makes the expected profits defined
--   - generalization: standing assumption n ≥ 4 farmers (p. 8) → any number n of farmers; reason: Lemma 2 does not use n ≥ 4; the statement specializes to every n ≥ 4
--   - encoding: each farmer receives the expected profit (in the equilibrium of Proposition 1) → the identities hold for every Bayesian Nash equilibrium of the game with informed set I; reason: by Proposition 1 an equilibrium exists and is unique almost surely, and expected profits depend only on the quantities up to null sets
--   - encoding: private signal x_i = u + ε_i, ε_i ∼ N(0, 1/γ), with γ = 0 meaning no private signal → observation s_i = √γ·u + ξ_i, ξ_i ∼ N(0, 1); reason: for γ > 0, s_i = √γ·x_i is a bijective rescaling with the same information; at γ = 0, s_i is independent of everything (no information), whereas u + ξ_i/√γ would be u under Lean's x/0 = 0
--   - encoding: the closed forms contain 1/γ, undefined at γ = 0 → Lean's 1/0 = 0, multiplied by A1² = B1² = 0; reason: at γ = 0 the formulas take their γ → 0 limits, so γ = 0 (no private signal) is covered with its intended values
--   - encoding: precisions α = 1/σ_u², β = 1/σ_r² of finite positive variances, γ = 1/σ_f² with γ = 0 allowed (p. 9) → hypotheses 0 < α, 0 < β, 0 ≤ γ; reason: the paper's parameter ranges; the shocks are built from an independent N(0,1) family on an arbitrary probability space
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14 (proof pp. 34–35)

import Mathlib
import Definitions.Def_FarmerInfoProvision_GaussianPrimitives
import Definitions.Def_FarmerInfoProvision_IsBNE
import Definitions.Def_FarmerInfoProvision_profitInformed
import Definitions.Def_FarmerInfoProvision_profitUninformed

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Lemma 2: ex-ante equilibrium profits of informed and uninformed farmers, and
`W^I > W^J`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14 (proof pp. 34–35): "For any given
information provision policy `(n1)`, each farmer `i ∈ I` receives an (ex-ante) expected profit:
`W^I(n1, β; γ) = b{A0² + A1²(1/α + 1/γ) + A2²(1/α + 1/β) + 2A1A2(1/α)}`, whereas each farmer
`j ∈ J` receives an (ex-ante) expected profit: `W^J(n1, β; γ) = b{B0² + B1²(1/α + 1/γ)}`.
Also, `W^I(n1, β; γ) > W^J(n1, β; γ)`."

For every informed set `I` (with `a, b, α, β > 0`, `γ ≥ 0`, `n1 = |I|`):
1. in every Bayesian Nash equilibrium `σ` of the game with informed set `I`, every farmer
   `i ∈ I` has expected profit `profitInformed a b c n n1 α β γ` and every farmer `j ∉ I` has
   expected profit `profitUninformed a b c n n1 α β γ`;
2. `profitUninformed a b c n n1 α β γ < profitInformed a b c n n1 α β γ`.

**Formalization Note.** Equilibrium as in `IsBNE` (unrestricted quantities, ex-ante best
responses over square integrable deviations). Clause 1 is stated for every equilibrium; by
Proposition 1 there is one and it is unique almost surely. At `γ = 0` the closed forms contain
Lean's junk `1/0 = 0`, multiplied by `A1² = B1² = 0`, so they take their `γ → 0` limits. The
proof's display of `W^I − W^J` on p. 35 lacks a factor `4`; only the sign, which is the
lemma's claim, is stated. The standing `n ≥ 4` is not needed. -/
theorem lemma_2_ex_ante_profits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (M : GaussianPrimitives P n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (I : Finset (Fin n)) :
    (∀ σ : Fin n → ℝ × ℝ → ℝ, IsBNE M a b c α β γ I σ →
      (∀ i ∈ I, expectedProfit M a b c α β γ I σ i =
        profitInformed a b c (n : ℝ) (I.card : ℝ) α β γ) ∧
      (∀ j ∉ I, expectedProfit M a b c α β γ I σ j =
        profitUninformed a b c (n : ℝ) (I.card : ℝ) α β γ)) ∧
    profitUninformed a b c (n : ℝ) (I.card : ℝ) α β γ <
      profitInformed a b c (n : ℝ) (I.card : ℝ) α β γ := by sorry

end FarmerInfoProvision
