-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_optSet_subset_Icc
-- name    : FeinbergLiang.ACOE.optSet_subset_Icc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:03:52.345985+00:00
-- url     : https://prove2.me/theorems/38b092fa-cffc-4193-bf9d-ded3900ba917
-- title:
--   Eq. (4.4) — the sets $\mathbb X_\alpha$ of minimizers of $v_\alpha$ are nonempty, compact, and lie in one bounded interval
-- statement:
--   For the inventory control problem, and $\alpha\in[0,1)$, let
--   $$\mathbb X_\alpha=\{x\in\mathbb R: v_\alpha(x)=m_\alpha\},\qquad m_\alpha=\inf_x v_\alpha(x).$$
--   Then:
--   1. each $\mathbb X_\alpha$ is nonempty and compact;
--   2. there are real numbers $x^*_L\le x^*_U$ such that
--   $$\mathbb X_\alpha\subseteq[x^*_L,x^*_U]\quad\text{for all }\alpha\in[0,1).\qquad(4.4)$$
--
--   The paper derives this from the inf-compactness of the cost, via Feinberg and Lewis (2007, Proposition 3.1(iv)) and Feinberg et al. (2012, Theorem 6). The interval $[x^*_L,x^*_U]$ is the one used to construct the dominating function $U$ in Lemma 4.6.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 577, Eq. (4.4) (citing Feinberg and Lewis 2007, Proposition 3.1(iv); Feinberg et al. 2012, Theorem 6)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- §4, p. 577, Eq. (4.4) (citing Feinberg and Lewis 2007, Proposition 3.1(iv), and Feinberg et
al. 2012, Theorem 6): for the inventory MDP each `X_α = {x : v_α(x) = m_α}`, `α ∈ [0, 1)`, is
nonempty and compact, and there is a bounded interval `[x*_L, x*_U]` containing all of them. -/
theorem optSet_subset_Icc (D : InventoryData) :
    (∀ α ∈ Set.Ico (0 : ℝ) 1,
      (optSet (inventoryMDP D) α).Nonempty ∧ IsCompact (optSet (inventoryMDP D) α)) ∧
    ∃ xL xU : ℝ, xL ≤ xU ∧ ∀ α ∈ Set.Ico (0 : ℝ) 1, optSet (inventoryMDP D) α ⊆ Set.Icc xL xU := by sorry

end FeinbergLiang.ACOE
