-- Prove2me | Theorems.Thm_BNCovPack_Covering_theorem_4_1
-- name    : BNCovPack.Covering.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:04.341674+00:00
-- url     : https://prove2.me/theorems/b57de23d-5953-424f-a729-5a018aa74b37
-- title:
--   Theorem 4.1 — phased online fractional covering guarantee
-- statement:
--   Let a finite normalized online covering instance have $n\ge1$ primal variables, positive costs $c_i$, nonnegative coefficients $a_{ik}$, and at least one positive coefficient in every arrived constraint. Fix $B>0$ and any nonempty arrival prefix of length $J$. A completed run of the phased scheme exists. For every completed run, its output $x$ covers each arrived constraint to $1/B$:
--
--   $$
--   \sum_i a_{ik}x_i\ge\frac1B\quad(k<J).
--   $$
--
--   For every nonnegative comparison vector $x''$ covering the same constraints to the unscaled level one, the output cost obeys
--
--   $$
--   \sum_i c_i x_i\le\frac{8\log(2n)}{B}\sum_i c_i x''_i.
--   $$
--
--   The paper states the competitive ratio as $O(\log n/B)$; its final displayed bound on page 9 gives the explicit coefficient $8\log(2n)/B$. The comparison vector is feasible for the normalized covering problem of Figure 1, so the result applies in particular to its optimum.
--
--   **Formalization Note** A run includes every continuous stopping time and restart, and the theorem asserts both existence and the guarantees for all such runs. The first constraint has a positive coefficient so the initial minimum is defined. Lean uses zero-based arrival indices and natural logarithms.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, pp. 8–9, Theorem 4.1 and closing display

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

/-- Theorem 4.1, pp. 8–9. The phased scheme has a completed run for every
feasible arrival prefix. Every such run covers that prefix to `1/B`, and its
cost is at most `8 log(2n)/B` times the cost of any nonnegative comparator
that covers the prefix to one. -/
theorem theorem_4_1 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) :
    (∃ s : State I m, Run inst B hm J s) ∧
    ∀ s : State I m, Run inst B hm J s →
      (∀ k : Fin m, k.val < J →
        1 / B ≤ ∑ i : I, inst.a i k * output s i) ∧
      (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) →
        (∀ k : Fin m, k.val < J → 1 ≤ ∑ i : I, inst.a i k * x'' i) →
        (∑ i : I, inst.c i * output s i) ≤
          (8 * Real.log (2 * (Fintype.card I : ℝ)) / B) *
            ∑ i : I, inst.c i * x'' i) := by sorry

end BNCovPack.Covering
