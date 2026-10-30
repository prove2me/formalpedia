-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_1_unique_bne
-- name    : FarmerInfoProvision.proposition_1_unique_bne
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:42.076584+00:00
-- url     : https://prove2.me/theorems/71bba548-9c60-4d6e-a40d-fa1c4019caa4
-- title:
--   Proposition 1: the linear profile (6)–(7) is the unique Bayesian Nash equilibrium (corrected: quantities unrestricted in sign)
-- statement:
--   Consider the production game: $n$ farmers choose quantities $q_i$ at unit cost $c$ and sell at the price $P(Q)=a-bQ+u$, $Q=\sum_i q_i$, where $a,b>0$ and the demand shock is $u\sim N(0,1/\alpha)$. Farmer $i$ privately observes a signal of $u$ of precision $\gamma\ge 0$ ($\gamma=0$: no private signal), and the farmers in a set $I$ also observe the public signal $y=u+\epsilon_r$, $\epsilon_r\sim N(0,1/\beta)$, all noises independent. Let $n_1=|I|$ and let $A_0=B_0$, $A_1$, $A_2$, $B_1$ be the coefficients (7) of Proposition 1. Assume $a,b,\alpha,\beta>0$ and $\gamma\ge0$. Then for every informed set $I$:
--
--   1. the linear profile
--   $$
--   q_i=A_0+A_1x_i+A_2y\ (i\in I),\qquad q_j=B_0+B_1x_j\ (j\notin I)
--   $$
--   is a Bayesian Nash equilibrium of the game;
--   2. every Bayesian Nash equilibrium produces, for every farmer, the same quantity as the linear profile almost surely.
--
--   This is the equilibrium on which Lemma 2's profit formulas and the central planner's problem rest.
--
--   **Formalization Note** Uniqueness is of the quantities as random variables, almost surely, as in the paper's argument ("$z_i=0$ almost surely", p. 34).
--
--   Differences from the source:
--   - correction: problems (2)–(3) maximize over quantities q ≥ 0 → quantities are unrestricted real numbers; reason: the paper's equilibrium (6)–(7) is infeasible under q ≥ 0: at n = 4, n1 = |I| = 1, α = β = γ = 1, a = 2, b = c = 1 (all assumptions hold), A2 = 1/10 > 0 and y is a nondegenerate Gaussian, so q_i = A0 + A1x_i + A2y < 0 with positive probability; with q ≥ 0 imposed, W^I and W^J are not equilibrium profits. Footnote 6 (p. 8) treats negative prices and quantities as a negligible convention
--   - encoding: interim best responses: maximize the conditional expected profit given the farmer's own signals → ex-ante best responses over Borel functions of the same signals with square-integrable output; reason: equivalent for square-integrable strategies (the ex-ante profit is the conditional one integrated over the signals); square integrability is what makes the expected profits defined
--   - generalization: standing assumption n ≥ 4 farmers (p. 8) → any number n of farmers; reason: the existence and uniqueness argument does not use n ≥ 4; the statement specializes to every n ≥ 4
--   - encoding: a unique equilibrium production quantity → every equilibrium's quantities equal the linear profile's almost surely; reason: strategies are determined only up to null sets of signals; the paper's own argument concludes z_i = 0 almost surely (p. 34)
--   - encoding: private signal x_i = u + ε_i, ε_i ∼ N(0, 1/γ), with γ = 0 meaning no private signal → observation s_i = √γ·u + ξ_i, ξ_i ∼ N(0, 1); reason: for γ > 0, s_i = √γ·x_i is a bijective rescaling with the same information; at γ = 0, s_i is independent of everything (no information), whereas u + ξ_i/√γ would be u under Lean's x/0 = 0
--   - encoding: precisions α = 1/σ_u², β = 1/σ_r² of finite positive variances, γ = 1/σ_f² with γ = 0 allowed (p. 9) → hypotheses 0 < α, 0 < β, 0 ≤ γ; reason: the paper's parameter ranges; the shocks are built from an independent N(0,1) family on an arbitrary probability space
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, displays (6)–(7), p. 12 (proof pp. 32–34)

import Mathlib
import Definitions.Def_FarmerInfoProvision_GaussianPrimitives
import Definitions.Def_FarmerInfoProvision_obs
import Definitions.Def_FarmerInfoProvision_IsBNE
import Definitions.Def_FarmerInfoProvision_linearProfile

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Proposition 1: the linear profile (6)–(7) is the unique Bayesian Nash equilibrium.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, displays (6)–(7), p. 12 (proof pp. 32–34):
"There exists a unique Bayesian Nash equilibrium production quantity `q_i` for farmer `i ∈ I`
(or farmer `j ∈ J`) that satisfies: `q_i(x_i, y) = A0 + A1 x_i + A2 y`, `∀i ∈ I`,
`q_j(x_j) = B0 + B1 x_j`, `∀j ∈ J`", with `A0 = B0 = (a − c)/(b(n + 1))`, `A1`, `A2`, `B1` and
`Ψ` as in (7) at `n1 = |I|`.

For every informed set `I` (with `a, b, α, β > 0`, `γ ≥ 0`):
1. the profile `linearProfile a b c n α β γ I` is a Bayesian Nash equilibrium of the game in
   which the farmers in `I` observe the public signal;
2. every Bayesian Nash equilibrium `σ` of that game produces, for every farmer `i`, the same
   quantity as the linear profile almost surely.

**Formalization Note.** Quantities are unrestricted real numbers and best responses are taken
ex ante over square integrable measurable functions of the farmer's observation (see `IsBNE`).
Uniqueness is of the quantities as random variables, almost surely, which is what the paper's
argument gives (p. 34, "`z_i = 0` almost surely"). The game observes `s_i = √γ·x_i`, and the
linear profile reads `x_i = s_i/√γ`; at `γ = 0` (no private signal) the private-signal
coefficients vanish. The standing `n ≥ 4` is not needed. -/
theorem proposition_1_unique_bne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (M : GaussianPrimitives P n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (I : Finset (Fin n)) :
    IsBNE M a b c α β γ I (linearProfile a b c n α β γ I) ∧
    ∀ σ : Fin n → ℝ × ℝ → ℝ, IsBNE M a b c α β γ I σ →
      ∀ i : Fin n, (fun ω => σ i (obs M α β γ I i ω)) =ᵐ[P]
        (fun ω => linearProfile a b c n α β γ I i (obs M α β γ I i ω)) := by sorry

end FarmerInfoProvision
