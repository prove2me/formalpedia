-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_pf_le_pe
-- name    : CarbonDoubleCount.Leader.pf_le_pe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:36.87527+00:00
-- url     : https://prove2.me/theorems/6198ea72-5ca4-42ce-9add-78d84a970947
-- title:
--   Proof of Proposition 5 (A.4), p. 26 — every feasible solution of P_F has value at most z^E
-- statement:
--   Let $(g^E,e^E)$ be an optimal solution of the effort-contracting problem $P_E$, with optimal value $z^E$. Then for every pair $(g,e)$ of emission-contingent payments $g_n(f)$ and efforts $e$ that is feasible for $P_F$, constraints (10)–(11),
--   $$V_N(e_N)-p\sum_{i\in\mathcal I}f_i(e)+\sum_{n\neq N}g_n\big(f(e)\big)\;\le\;z^E.$$
--
--   This is the upper-bound half of Proposition 5: contracting on emissions cannot beat contracting on efforts. The paper phrases it as "$P_F$ is a constrained version of $P_E$".
--
--   **Formalization Note.** No regularity hypothesis is needed. The bound does not come from an inclusion of feasible sets, since $P_F$'s payments are functions of $f(e)$ and $P_E$'s of $e_n$. It comes from the participation constraint (10) together with the reduction of $P_E$ to the first-best problem at price $p$.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 26, proof of Proposition 5 (App. A.4), "Finally, … it will achieve profits z^E, which is an upper bound since P_F is a constrained version of P_E."

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem pf_le_pe
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE) :
    ∀ (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ),
      PFFeasible A V f L πbar g e → pfObjective V f p L g e ≤ peObjective V f p L gE eE := by sorry

end CarbonDoubleCount.Leader
