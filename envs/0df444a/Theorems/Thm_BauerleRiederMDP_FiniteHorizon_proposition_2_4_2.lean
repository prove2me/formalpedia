-- Prove2me | Theorems.Thm_BauerleRiederMDP_FiniteHorizon_proposition_2_4_2
-- name    : BauerleRiederMDP.FiniteHorizon.proposition_2_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:21.829887+00:00
-- url     : https://prove2.me/theorems/34da2865-9741-4cea-bfa8-825800380621
-- title:
--   Proposition 2.4.2 — an upper bounding function bounds $\delta^N_n$ and implies $(A_N)$ (corrected: the bound, without measurability of $\delta^N_n$)
-- statement:
--   Let the Markov Decision Model have an upper bounding function $b$. Then for each $n=0,\dots,N$ there is $c\in\mathbb R_+$ with
--
--   $$\delta^N_n(x)\le c\,b(x)\qquad\text{for all } x\in E,$$
--
--   and the Integrability Assumption $(A_N)$ is satisfied.
--
--   Upper bounding functions are the book's standard way of verifying $(A_N)$, and they also drive the infinite-horizon theory of Chapter 7.
--
--   **Formalization Note.** The bound is the book's second description of $\mathbb B_b$ on p.28, and is what its proof of this proposition establishes.
--
--   Differences from the source:
--   - correction: δ^N_n ∈ IB_b, where IB_b is a set of measurable functions → δ^N_n ≤ c·b for some c ≥ 0, without measurability of δ^N_n; reason: δ^N_n need not be measurable. Take E = A = [0,1] with the Borel sets, N = 1, D_0 = E × A, g_1 = 0, any kernel Q_0, and r_0 the indicator of a Borel set B ⊂ [0,1]² whose projection to the first coordinate is not Borel. Then b ≡ 1 is an upper bounding function, and δ^1_0 is the indicator of that projection (use constant decision rules), which is not measurable. The book's proof shows exactly the bound: 'we have to show that δ^N_n(x) ≤ cb(x)'
--   - encoding: Q_n and r_n are defined on D_n → Q_n and r_n are defined on E × A (MDPFinance.Bellman.MarkovDecisionModel); reason: D_n is measurable, so every book model extends (for example by δ_x and 0), and values off D_n enter no statement
--   - encoding: 𝔼^π_{nx} is the expectation under the conditional probability ℙ^π(· | X_n = x) → the expectation under the kernel pathKernel, forward composition of the Q_k, recording states and actions; reason: this is the regular version of the conditional law, defined at every x
--   - encoding: E and A are sets → E and A lie in one universe, as in MDPFinance.Bellman.Hist; reason: a Lean universe convention; no mathematical instance is lost, since a space can be lifted
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 2.4.2, p.29

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- Proposition 2.4.2 (Bäuerle & Rieder (2011), p.29, PDF 44). If the Markov Decision Model has an
upper bounding function `b`, then `δ^N_n(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+`, for each
`n = 0, …, N`, and the Integrability Assumption (A_N) is satisfied.

**Formalization Note.** The bound is the book's second description of `IB_b` (p.28). The other
half of `δ^N_n ∈ IB_b`, measurability of `δ^N_n`, is false in general: see the Differences list of
this item. -/
theorem proposition_2_4_2 {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (hb : IsUpperBoundingFunction M b) :
    (∀ n ≤ N, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, deltaN M n x ≤ ENNReal.ofReal (c * b x)) ∧
    IntegrabilityAssumption M := by sorry

end BauerleRiederMDP.FiniteHorizon
