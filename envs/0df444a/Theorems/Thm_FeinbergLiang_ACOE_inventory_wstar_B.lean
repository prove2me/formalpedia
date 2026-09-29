-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_inventory_wstar_B
-- name    : FeinbergLiang.ACOE.inventory_wstar_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:03:16.019986+00:00
-- url     : https://prove2.me/theorems/7e4c5ab6-6ada-4320-a8cd-86dce9841c35
-- title:
--   Inventory control satisfies Assumptions W* and B (Feinberg–Lewis 2015, cited on p. 576)
-- statement:
--   Consider the periodic-review inventory control problem with fixed ordering cost $K\ge0$, per-unit cost $\bar c>0$, convex holding/backordering cost $h$ with $h(x)\to\infty$ as $|x|\to\infty$ (normalized so that $h\ge0$ and $h(0)=0$), and i.i.d. nonnegative demands $D$ with $\mathbb E[h(x-D)]<\infty$ for all $x$ and $P(D>0)>0$. Take state space $\mathbb R$, action space $[0,\infty)$, one-step cost
--   $$c(x,a)=K I_{\{a>0\}}+\bar c a+\mathbb E[h(x+a-D)],$$
--   and transitions $x\mapsto x+a-D$. This MDP satisfies:
--   1. Assumption W*: the cost is $\mathbb K$-inf-compact and bounded below, and the transition probability is weakly continuous;
--   2. Assumption B: $w^*=\inf_x w(x)<\infty$, and $\sup_{\alpha\in[0,1)}u_\alpha(x)<\infty$ for every $x$.
--
--   The paper cites this fact from Feinberg and Lewis (2015, Corollary 6.1, Proposition 6.3). It is what allows the general results of §3 to be applied to inventory control.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 576, Section 4 (citing Feinberg and Lewis 2015, Corollary 6.1, Proposition 6.3)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- §4, p. 576 (citing Feinberg and Lewis 2015, Corollary 6.1, Proposition 6.3): the MDP of the
inventory control problem satisfies Assumptions W* and B. -/
theorem inventory_wstar_B (D : InventoryData) :
    AssumptionWStar (inventoryMDP D) ∧ AssumptionB (inventoryMDP D) := by sorry

end FeinbergLiang.ACOE
