-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_pe_reduction
-- name    : CarbonDoubleCount.Leader.pe_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:46.635284+00:00
-- url     : https://prove2.me/theorems/77f2a2ce-e8c8-4230-99c4-0b73751af146
-- title:
--   §5, p. 15 — contracting on efforts reduces P_E to the first-best problem (1) at price p, minus the reservation profits
-- statement:
--   Let firm $N$ be the carbon leader, paying carbon price $p$, and let $\bar\pi_n$ be the reservation profits of the other firms. Let $(g^E,e^E)$ be an optimal solution of the leader's effort-contracting problem $P_E$ (6)–(8), and write $z^E$ for its optimal value. Then
--   $$z^E=\sum_{n\in\mathcal N}V_n(e^E_n)-p\sum_{i\in\mathcal I}f_i(e^E)-\sum_{n\neq N}\bar\pi_n,$$
--   and $e^E$ maximizes the social value at price $p$ over the effort box:
--   $$\sum_{n}V_n(e_n)-p\sum_{i}f_i(e)\;\le\;\sum_{n}V_n(e^E_n)-p\sum_{i}f_i(e^E)\qquad\text{for every } e\in[0,A]^M.$$
--
--   In words, a leader who can contract on efforts solves the social planner's first-best problem (1), with its own carbon price $p$ in place of the societal cost $p_S$, and its profit is that maximum minus the constant $\sum_{n\neq N}\bar\pi_n$. This is the benchmark against which Proposition 5 measures emission-contingent contracting.
--
--   **Formalization Note.** No differentiability, convexity or influence-matrix hypothesis is needed and none is assumed. The page's intermediate equality $V_n(e_n)-\bar\pi_n=-c_n(e_n)$ holds only when $\bar\pi_n=\bar V_n$ and is not part of the statement.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 15, §5, paragraph after (6)–(8) ("Since the carbon leader can contract on efforts, …")

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem pe_reduction
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE) :
    peObjective V f p L gE eE = socialValue V f p eE - ∑ n ∈ univ.erase L, πbar n ∧
      ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, socialValue V f p e ≤ socialValue V f p eE := by sorry

end CarbonDoubleCount.Leader
