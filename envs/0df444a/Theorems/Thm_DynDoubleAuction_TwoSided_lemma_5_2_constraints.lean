-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_lemma_5_2_constraints
-- name    : DynDoubleAuction.TwoSided.lemma_5_2_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:55.243226+00:00
-- url     : https://prove2.me/theorems/4d53c305-f693-4105-bb0e-d5bdc687f518
-- title:
--   Lemma 5.2 — incentive, participation and promise constraints
-- statement:
--   At a period $1\le t\le T$, suppose all agents have the same current promise $c\in[0,\bar w^t]$. For the paper's allocation and transfers, every report profile in the value box yields allocations in $[0,1]$ and satisfies period individual rationality, nonnegative transfers, and weak supply balance:
--
--   $$\phi_i(v_i,v;w)\ge0,\quad z_i(v;w)\ge0,\quad\sum_{i=1}^nq_i(v;w)\le q_0(v;w).$$
--
--   For every agent, the expected sum of truthful period utility and continuation utility equals $c$ (promise keeping). Reporting the true value maximizes that sum against every fixed profile of other reports (dynamic incentive compatibility).
--
--   This is the constraint part of Lemma 5.2. It connects the specified rule to the feasibility conditions used by the profit theorem.
--
--   **Formalization Note** The incentive comparison quantifies over both true and alternative values in $[0,\bar v]$; it is pointwise in the other agents' reports. The balance condition is the weak inequality stated for the paper's boundary rule.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), pp. 25–28, Lemma 5.2

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- Lemma 5.2: participation, transfers, weak supply balance, promise keeping, and incentives. -/
theorem lemma_5_2_constraints {n : ℕ} (M : Market n) (hM : Standing M)
    (T t : ℕ) (ht : 1 ≤ t ∧ t ≤ T) (c : ℝ)
    (hc : 0 ≤ c ∧ c ≤ wbar M T t) :
    (∀ v : Fin (n + 1) → ℝ,
      (∀ j, v j ∈ Set.Icc 0 M.vbar) →
      (∀ j, (rule M T t (fun _ => c) v).q j ∈ Set.Icc 0 1 ∧
        0 ≤ periodUtility (rule M T t (fun _ => c) v) j (v j) ∧
        0 ≤ (rule M T t (fun _ => c) v).z j) ∧
      (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
        (rule M T t (fun _ => c) v).q i) ≤
        (rule M T t (fun _ => c) v).q 0) ∧
    (∀ j : Fin (n + 1),
      (∫ v, periodUtility (rule M T t (fun _ => c) v) j (v j) +
        (rule M T t (fun _ => c) v).u j ∂M.F) = c) ∧
    (∀ j : Fin (n + 1), ∀ vhat : Fin (n + 1) → ℝ,
      (∀ i, vhat i ∈ Set.Icc 0 M.vbar) →
      ∀ x y : ℝ, x ∈ Set.Icc 0 M.vbar → y ∈ Set.Icc 0 M.vbar →
      let truthful := rule M T t (fun _ => c) (Function.update vhat j x)
      let deviating := rule M T t (fun _ => c) (Function.update vhat j y)
      periodUtility deviating j x + deviating.u j ≤
        periodUtility truthful j x + truthful.u j) := by sorry
end DynDoubleAuction.TwoSided
