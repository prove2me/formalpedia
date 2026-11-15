-- Prove2me | Theorems.Thm_APFB07b_rate_is_held_after_a_costly_start
-- name    : APFB07b.rate_is_held_after_a_costly_start
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:06.657228+00:00
-- url     : https://prove2.me/theorems/466f4c4e-d4bb-403b-95c4-fa3bfb832eba
-- title:
--   A costly pinned history can distinguish equal present records
-- statement:
--   For finite histories satisfying A2 and unique-minimum BW, assume sum cost, a single costly pinned start, a compatible mirror fixing that start, and a genuinely different moment two steps on. With supplied history-to-state/readout/hold correspondences and quotient descent of later records, the next moment and its mirror have equal present records but distinct physical classes. All these bindings remain hypotheses.
-- source:
--   Sib v44 Theorems/Thm_APFB07_moves.lean:107

import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB07b.rate_is_held_after_a_costly_start {Interface : Type*} {T : Type*} [Fintype T]
    [DecidableEq T] {X : Type uX} {Process : Type uP} {R : Type uR}
    (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → ℝ)
    (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T) (next : T → T)
    (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (t0 : Interface → T) (e : Interface → R)
    (hadm : ∀ i r, originalAdmissible i r ↔ r (t0 i) = e i)
    (hfix : ∀ i, sigma (t0 i) = t0 i)
    (i : Interface) (v : R) (hv : c i v < c i (e i)) (h3 : next (next (t0 i)) ≠ t0 i)
    (profile : X → Process → Prop) (now : X → R) (D : X → X) (o : T → X)
    (hrec : ∀ t : T, realized i t = now (o t)) (ho : ∀ t : T, o (next t) = D (o t))
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r)) :
    now (o (sigma (next (t0 i)))) = now (o (next (t0 i))) ∧
      APFB01.physicalClass profile (o (sigma (next (t0 i)))) ≠
        APFB01.physicalClass profile (o (next (t0 i))) := by sorry
