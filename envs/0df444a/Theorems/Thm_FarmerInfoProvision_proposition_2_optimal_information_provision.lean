-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_optimal_information_provision
-- name    : FarmerInfoProvision.proposition_2_optimal_information_provision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:41.67287+00:00
-- url     : https://prove2.me/theorems/b6e64543-d622-4dbb-b551-4dcd33363830
-- title:
--   Proposition 2: informing exactly one farmer is optimal iff $V(n,\beta;\gamma)>0$, and informing nobody otherwise (corrected: quantities unrestricted in sign)
-- statement:
--   Consider the production game: $n$ farmers choose quantities $q_i$ at unit cost $c$ and sell at the price $P(Q)=a-bQ+u$, $Q=\sum_i q_i$, where $a,b>0$ and the demand shock is $u\sim N(0,1/\alpha)$. Farmer $i$ privately observes a signal of $u$ of precision $\gamma\ge 0$ ($\gamma=0$: no private signal), and the farmers in a set $I$ also observe the public signal $y=u+\epsilon_r$, $\epsilon_r\sim N(0,1/\beta)$, all noises independent. Assume $n\ge4$, $a,b,\alpha,\beta>0$ and $\gamma\ge0$. Let
--
--   $$
--   \begin{aligned}
--   V(n,\beta;\gamma)={}&16\alpha^4+16\alpha^3(\beta+3\gamma)+4\alpha^2\gamma\bigl[(7+n)\beta+(12+2n-n^2)\gamma\bigr]\\
--   &+4\alpha\gamma^2\bigl[(4+n)\beta+(5+2n-n^2)\gamma\bigr]-(n^2-2n-3)\gamma^3(\beta+\gamma),
--   \end{aligned}
--   $$
--
--   and $n_1^*=1$ if $V(n,\beta;\gamma)>0$, $n_1^*=0$ otherwise. Then:
--
--   1. for every set $I$ of informed farmers the game has a Bayesian Nash equilibrium;
--   2. for all informed sets $I$, $I'$ with $|I'|=n_1^*$, and all equilibria $\sigma$ of the game with $I$ and $\sigma'$ of the game with $I'$, the farmers' total expected profit under $\sigma$ is at most that under $\sigma'$;
--   3. it is strictly smaller whenever $|I|\ne|I'|$ and either $|I|\ge2$ or $V(n,\beta;\gamma)\ne0$.
--
--   So the central planner should give the public signal to exactly one farmer when $V>0$ and to nobody when $V<0$; informing two or more farmers is never optimal. Since $V>0$ when private signals are imprecise or the market is small, and $V<0$ when $\gamma$ or $n$ is large, wide dissemination of public information does not maximize farmer welfare.
--
--   Differences from the source:
--   - correction: problems (2)–(3) maximize over quantities q ≥ 0 → quantities are unrestricted real numbers; reason: the paper's equilibrium (6)–(7) is infeasible under q ≥ 0: at n = 4, n1 = |I| = 1, α = β = γ = 1, a = 2, b = c = 1 (all assumptions hold), A2 = 1/10 > 0 and y is a nondegenerate Gaussian, so q_i = A0 + A1x_i + A2y < 0 with positive probability; with q ≥ 0 imposed, W^I and W^J are not equilibrium profits. Footnote 6 (p. 8) treats negative prices and quantities as a negligible convention
--   - encoding: interim best responses: maximize the conditional expected profit given the farmer's own signals → ex-ante best responses over Borel functions of the same signals with square-integrable output; reason: equivalent for square-integrable strategies (the ex-ante profit is the conditional one integrated over the signals); square integrability is what makes the expected profits defined
--   - reading: n1 ∈ [0, n] in problem (5) → informed sets I, with n1 = |I| ∈ {0, …, n}; reason: n1 = |I| is a number of farmers (pp. 9, 11) and the proof compares the integers 0, 1, 2; over the real interval the statement is false (n = 4, α = β = γ = 1: W(0.525) > W(1) > W(0))
--   - generalization: the policy is the number n1 of informed farmers → every informed set I of size n1, and every equilibrium of each game; reason: the farmers are ex-ante identical, so the statement for every set of a given size specializes to the paper's statement about the number n1
--   - reading: the optimal information provision policy n1* satisfies n1* = 1 if V > 0, 0 if V ≤ 0 → existence of an equilibrium for every I; weak optimality of |I'| = n1*; strict optimality against |I| ≥ 2 and, when V ≠ 0, against the other of {0, 1}; reason: 'the optimal' asserts uniqueness, which holds except at V = 0, where the policies 0 and 1 tie and the paper picks 0; existence keeps the optimality clauses from being vacuous
--   - encoding: private signal x_i = u + ε_i, ε_i ∼ N(0, 1/γ), with γ = 0 meaning no private signal → observation s_i = √γ·u + ξ_i, ξ_i ∼ N(0, 1); reason: for γ > 0, s_i = √γ·x_i is a bijective rescaling with the same information; at γ = 0, s_i is independent of everything (no information), whereas u + ξ_i/√γ would be u under Lean's x/0 = 0
--   - encoding: precisions α = 1/σ_u², β = 1/σ_r² of finite positive variances, γ = 1/σ_f² with γ = 0 allowed (p. 9) → hypotheses 0 < α, 0 < β, 0 ≤ γ; reason: the paper's parameter ranges; the shocks are built from an independent N(0,1) family on an arbitrary probability space
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14, with problem (5), p. 11 (proof pp. 35–36)

import Mathlib
import Definitions.Def_FarmerInfoProvision_GaussianPrimitives
import Definitions.Def_FarmerInfoProvision_IsBNE
import Definitions.Def_FarmerInfoProvision_welfare
import Definitions.Def_FarmerInfoProvision_provisionIndex
import Definitions.Def_FarmerInfoProvision_optimalCount

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Proposition 2: informing exactly one farmer is optimal iff `V(n, β; γ) > 0`, and informing
nobody otherwise.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14 (proof pp. 35–36): "The optimal
information provision policy `n1*` satisfies: `n1* = 1` if `V(n, β; γ) > 0`; `0` if
`V(n, β; γ) ≤ 0`, where `V(n, β; γ) = 16α⁴ + 16α³(β + 3γ) + 4α²γ[(7 + n)β + (12 + 2n − n²)γ]
+ 4αγ²[(4 + n)β + (5 + 2n − n²)γ] − (n² − 2n − 3)γ³(β + γ)`", where `n1*` solves the central
planner's problem (5), p. 11: "`S* = max_{n1 ∈ [0,n]} W(n1, β; γ) ≡ max {n1 W^I(n1, β; γ) +
(n − n1) W^J(n1, β; γ)}`", `W^I`, `W^J` being the farmers' ex-ante equilibrium profits in the
Cournot game of §3 (pp. 8–11).

The game: `n ≥ 4` farmers; the price is `a − bQ + u` with `a, b > 0` and `u ∼ N(0, 1/α)`; farmer
`i` sees a private signal of precision `γ ≥ 0` (`γ = 0`: none), and the farmers in the set `I`
also see the public signal `y = u + ϵ_r`, `ϵ_r ∼ N(0, 1/β)`, `β > 0`. Let `n1* = 1` if
`V(n, β; γ) > 0` and `n1* = 0` otherwise. Then:
1. for every informed set `I` the game has a Bayesian Nash equilibrium;
2. for all informed sets `I`, `I'` with `|I'| = n1*` and all equilibria `σ` of the game with `I`
   and `σ'` of the game with `I'`, total expected profit under `σ` is at most that under `σ'`;
3. it is strictly smaller whenever `|I| ≠ |I'|` and either `|I| ≥ 2` or `V(n, β; γ) ≠ 0`.

**Formalization Note.** (a) Quantities are unrestricted real numbers: problems (2)–(3) print
`q ≥ 0`, but the paper's equilibrium is Gaussian and negative with positive probability, so
with `q ≥ 0` the paper's `W^I`, `W^J` are not equilibrium profits (see `IsBNE`). (b) Best
responses are ex ante, over square integrable measurable functions of the farmer's signals
(see `IsBNE`). (c) The policy is a set `I` of farmers; `n1 = |I|` ranges over `0, …, n`, not
over the real interval `[0, n]` printed in (5), on which the statement is false. (d) "The
optimal policy" is clauses 2 and 3; at `V = 0` the policies of sizes `0` and `1` tie.
(e) The private observation is `s_i = √γ·u + ξ_i`, a rescaling of the paper's `x_i` that
encodes `γ = 0` as "no private signal" (see `privateObs`). (f) The cost `c` is unrestricted,
as in the paper. -/
theorem proposition_2_optimal_information_provision
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) (M : GaussianPrimitives P n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∀ I : Finset (Fin n), ∃ σ : Fin n → ℝ × ℝ → ℝ, IsBNE M a b c α β γ I σ) ∧
    ∀ (I I' : Finset (Fin n)) (σ σ' : Fin n → ℝ × ℝ → ℝ),
      IsBNE M a b c α β γ I σ → IsBNE M a b c α β γ I' σ' →
      I'.card = optimalCount (n : ℝ) α β γ →
      welfare M a b c α β γ I σ ≤ welfare M a b c α β γ I' σ' ∧
      (I.card ≠ I'.card → (2 ≤ I.card ∨ provisionIndex (n : ℝ) α β γ ≠ 0) →
        welfare M a b c α β γ I σ < welfare M a b c α β γ I' σ') := by sorry

end FarmerInfoProvision
