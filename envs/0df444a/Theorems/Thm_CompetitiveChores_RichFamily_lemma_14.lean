-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_14
-- name    : CompetitiveChores.RichFamily.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:31.685007+00:00
-- url     : https://prove2.me/theorems/82434004-d550-49b5-bc10-f324f7dc1a16
-- title:
--   Lemma 14 — Pareto optimal ⇔ no simple profitable trading cycle ⇔ G_z ⊆ G_τ(v) ⇔ maximal weighted welfare
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ be a matrix of values and $z$ a feasible allocation. The following statements are equivalent:
--   1. $z$ is Pareto optimal.
--   2. $z$ has no simple profitable trading cycle.
--   3. There is $\tau\in\mathbb R^n_{>0}$ such that the consumption graph $G_z$ is a subgraph of the MWW graph $G_\tau(v)$.
--   4. There is $\tau\in\mathbb R^n_{>0}$ such that $z$ maximizes the weighted utilitarian welfare among all feasible allocations:
--   $$\sum_{i\in[n]}\tau_i\,u_i(y_i)\le\sum_{i\in[n]}\tau_i\,u_i(z_i)\qquad\text{for every feasible } y.$$
--
--   The lemma translates Pareto optimality, a statement about all feasible allocations, into a combinatorial condition on the consumption graph; it is the bridge between the Pareto frontier and MWW graphs used in Lemmas 18, 19 and 22.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 17, §2.5, Lemma 14 (proof in Appendix B, pp. 52–53)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 14, p. 17: for `v ∈ ℝ^{n×m}_{<0}` and a feasible allocation `z`, the following are equivalent:
(1) `z` is Pareto optimal; (2) `z` has no simple profitable trading cycle; (3) the consumption graph
of `z` is a subgraph of the MWW graph `G_τ(v)` for some `τ ∈ ℝ^n_{>0}`; (4) `z` maximizes the weighted
utilitarian welfare `∑_i τ_i u_i(z_i)` among all feasible allocations for some `τ ∈ ℝ^n_{>0}`. -/
theorem lemma_14 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (z : Fin n → Fin m → ℝ)
    (hz : IsFeasible z) :
    List.TFAE
      [ IsParetoOptimal v z,
        ¬ ∃ C : BPath n m, C.IsSimpleCycle ∧ IsProfitableTradingCycle v z C,
        ∃ τ : Fin n → ℝ, (∀ i, 0 < τ i) ∧ consumptionGraph z ⊆ mwwGraph v τ,
        ∃ τ : Fin n → ℝ, (∀ i, 0 < τ i) ∧ ∀ y, IsFeasible y →
          ∑ i, τ i * utilityProfile v y i ≤ ∑ i, τ i * utilityProfile v z i ] := by sorry

end CompetitiveChores.RichFamily
