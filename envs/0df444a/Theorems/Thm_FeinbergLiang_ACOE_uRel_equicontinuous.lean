-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_uRel_equicontinuous
-- name    : FeinbergLiang.ACOE.uRel_equicontinuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:07:03.534327+00:00
-- url     : https://prove2.me/theorems/cc28a7e0-6648-4c5e-bf84-af1f293efd72
-- title:
--   Lemma 4.7 — the discounted relative value functions $u_{\alpha_n}$ of the inventory problem are equicontinuous
-- statement:
--   Consider the inventory control problem, and let $\{\alpha_n\uparrow1\}$ be a sequence of nonnegative discount factors with $\alpha_1>\alpha^*$. Then every $u_{\alpha_n}$ is real-valued, and the family $\{u_{\alpha_n}\}_{n\ge1}$ is equicontinuous on $\mathbb R$: for each $x$ and $\epsilon>0$ there is a neighbourhood $G$ of $x$ with
--   $$|u_{\alpha_n}(y)-u_{\alpha_n}(x)|<\epsilon\quad\text{for all }y\in G\text{ and all }n.$$
--
--   This is Assumption EC(i) for the inventory problem, and it is the main technical step of the paper.
--
--   **Formalization Note.** The paper indexes the sequence from $\alpha_1$, and Lean from `α 0`. The sequence condition means values in $[0,1)$, nondecreasing, with limit $1$. $\alpha^*$ is an extended real.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 580, Lemma 4.7

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Lemma 4.7 (Feinberg–Liang 2022, p. 580). For each sequence `α_n ↑ 1` of nonnegative discount
factors with `α_1 > α*` (Lean's `α 0`), the relative value functions `u_{α_n}` of the inventory
MDP are real-valued and the family `{u_{α_n}}` is equicontinuous on `ℝ`. -/
theorem uRel_equicontinuous (D : InventoryData) (α : ℕ → ℝ) (hα : IsDiscountSeq α)
    (hα0 : alphaStar D < (α 0 : EReal)) :
    (∀ n x, uRel (inventoryMDP D) (α n) x ≠ ⊤) ∧
    Equicontinuous (fun n x => (uRel (inventoryMDP D) (α n) x).toReal) := by sorry

end FeinbergLiang.ACOE
