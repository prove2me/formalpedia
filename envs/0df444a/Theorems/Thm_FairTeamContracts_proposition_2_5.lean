-- Prove2me | Theorems.Thm_FairTeamContracts_proposition_2_5
-- name    : FairTeamContracts.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:14.24807+00:00
-- url     : https://prove2.me/theorems/0085edab-696e-4b06-9ad4-3d3d8ca38736
-- title:
--   Proposition 2.5 — uniqueness of the equilibrium after a swap (submodular $f$)
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be submodular, and let $(S,\alpha)$ be a team contract in which all agents of $S$ are incentivized to exert costly effort. For any pair of agents $i,j\in S$, let $\hat\alpha$ be the contract obtained by swapping their shares, $\hat\alpha_i=\alpha_j$ and $\hat\alpha_j=\alpha_i$. Then $\hat\alpha$ has exactly one pure Nash equilibrium:
--
--   $$|\mathcal E_{S,\hat\alpha}|=1.$$
--
--   This is what makes the equilibrium $S_{i,j}$ after a swap well defined for submodular rewards, and with it the fairness test of Definition 2.2 a statement about a single set.
--
--   Differences from the source:
--   - encoding: all agents in S are incentivized to exert costly effort (αᵢ ≥ cᵢ/f(i|S∖{i})) → IsFeasible: αᵢ·f(S) − cᵢ ≥ αᵢ·f(S∖{i}) for i ∈ S; reason: the paper's own display on p.8; equivalent under 0/0 = 0, c/0 = ∞
--   - encoding: submodular (Definition 2.4, for every i ∈ [n]) → published IsSubmodular (diminishing returns for e ∉ B) together with the monotonicity of IsSuccessFn; reason: Definition 2.4's extra cases i ∈ S′ only say a marginal is ≥ 0, which is monotonicity; same class of functions
--   - encoding: |E_{S,α̂}| = 1 → ∃! E, IsPNE f c S (α ∘ swap i j) E; reason: the same statement
--   - generalization: a pair of agents i, j ∈ S → any i, j ∈ S, including i = j; reason: for i = j the swap is the identity and the unique equilibrium is S (feasibility and submodularity put every agent in every equilibrium); for i ≠ j it is the page's statement
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Proposition 2.5, p.10 (proof: Appendix A, p.38)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsTeamContract
import Definitions.Def_FairTeamContracts_IsFeasible
import Definitions.Def_FairTeamContracts_IsPNE

namespace FairTeamContracts

/-- **Proposition 2.5 (Uniqueness of Equilibrium for Submodular)** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…),
Proposition 2.5, p.10; proof in Appendix A, p.38). For a submodular success function `f`,
nonnegative costs, and a team contract `(S, α)` in which all agents of `S` are incentivized to
exert effort, for any pair `i, j ∈ S` the contract `α̂` obtained by swapping `αᵢ` and `αⱼ` has
exactly one pure Nash equilibrium: `|E_{S,α̂}| = 1`.

**Formalization Note.** Submodularity is the published `SubsamplingSM.Offline.IsSubmodular`
(diminishing returns for `e ∉ B`); with monotonicity it is the paper's Definition 2.4. "All agents
in `S` are incentivized" is `IsFeasible`. The swapped contract is `α ∘ Equiv.swap i j`. -/
theorem proposition_2_5 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (α : Fin n → ℝ) (hα : IsTeamContract S α) (hfeas : IsFeasible f c S α)
    (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S) :
    ∃! E : Finset (Fin n), IsPNE f c S (α ∘ Equiv.swap i j) E := by sorry

end FairTeamContracts
