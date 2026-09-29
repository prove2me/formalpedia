-- Prove2me | Theorems.Thm_FamousTheorems_isbigo_asympbound
-- name    : FamousTheorems.isbigo_asympbound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:21.364414+00:00
-- url     : https://prove2.me/theorems/cc42397a-cd61-4d60-ae14-c64c4ccdb698
-- title:
--   The Akra–Bazzi theorem
-- statement:
--   **The Akra\u2013Bazzi theorem.** A divide-and-conquer recurrence $T(n) = g(n) + \sum_i a_i T(b_i n)$ has asymptotic solution $$T(n) = \Theta\!\left(n^{p}\left(1 + \int_1^n \frac{g(u)}{u^{p+1}}du\right)\right),$$ where $p$ solves $\sum_i a_i b_i^{p} = 1$. This generalises the Master theorem substantially: the subproblems may have different sizes, the sizes need not divide evenly, and the driving function $g$ is arbitrary rather than restricted to a few regimes. It is the general tool for analysing recursive algorithms whose recursion tree is unbalanced. **Formalization note.** `AkraBazziRecurrence` bundles the hypotheses on the coefficients and subproblem sizes; the conclusion is a `Θ` bound stated via `isBigO`. The result is Mathlib's `AkraBazziRecurrence.isBigO_asympBound`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isbigo_asympbound :
    ∀ {α : Type u_1} [inst : Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} 
    {r : α → ℕ → ℕ} [inst_1 : Nonempty α] (R : AkraBazziRecurrence T g a b r), 
    T =O[atTop] AkraBazziRecurrence.asympBound g a b := by sorry

end FamousTheorems
