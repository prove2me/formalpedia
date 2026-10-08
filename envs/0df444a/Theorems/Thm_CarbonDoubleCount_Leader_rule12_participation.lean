-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_rule12_participation
-- name    : CarbonDoubleCount.Leader.rule12_participation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:22.105105+00:00
-- url     : https://prove2.me/theorems/143753d2-594f-43b1-bc05-b69e12f1b7e7
-- title:
--   Proof of Proposition 5 (A.4), p. 26 — under rule (12) the efforts e^E satisfy the participation constraint (10) with equality
-- statement:
--   In the setting of Proposition 5, let $(g^E,e^E)$ be optimal for $P_E$ and let $g_n$ be the linear payment rule (12) built from $e^E$. Then for every firm $n\ne N$,
--   $$V_n(e^E_n)-g_n\big(f(e^E)\big)=\bar\pi_n,$$
--   so the participation constraint (10) of $P_F$ holds at $e^E$, with equality.
--
--   This is the first of the three steps by which the appendix shows that rule (12) and $e^E$ are feasible for $P_F$; the constant $k_n$ of (12) is chosen exactly to make it hold.
--
--   **Formalization Note.** The statement carries all standing hypotheses of Proposition 5, including the interiority of $e^E$, although the identity itself is algebraic.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 26, proof of Proposition 5 (App. A.4), "First, from the definition of k_n …"

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem rule12_participation
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ) (hA : 0 < A) (hp : 0 ≤ p)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (CarbonDoubleCount.Planner.firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (CarbonDoubleCount.Planner.firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (CarbonDoubleCount.Planner.effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (CarbonDoubleCount.Planner.effortBox A))
    (hfnonneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ) (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ n i, (B n i = 1 ↔ ∑ j, dEff (fun e => f e i) e n j < 0))
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE)
    (hint : ∀ n j, 0 < eE n j ∧ eE n j < A) :
    ∀ n, n ≠ L → V n (eE n) - rule12 V f p B πbar eE n (f eE) = πbar n := by sorry

end CarbonDoubleCount.Leader
