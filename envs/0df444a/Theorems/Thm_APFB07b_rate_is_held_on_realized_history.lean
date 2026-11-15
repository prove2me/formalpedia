-- Prove2me | Theorems.Thm_APFB07b_rate_is_held_on_realized_history
-- name    : APFB07b.rate_is_held_on_realized_history
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:09:24.02391+00:00
-- url     : https://prove2.me/theorems/dc850ea5-c92f-4647-9a17-2d81680ba80f
-- title:
--   A symmetric selected history can distinguish equal present records
-- statement:
--   With A2/BW on finite histories, sum cost and admissibility under a supplied mirror permutation force mirrored realized records to agree. If mirror and next obey the displayed compatibility equation and a record changes over two steps, supplied state/readout/hold correspondence and later-record descent yield mirrored next states with equal present records but distinct physical classes.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_history_retraces.lean:99

import Theorems.Thm_APFB07b_realized_fixed_by_cost_symmetry
import Theorems.Thm_APFB07b_realized_has_no_rate_of_present_records
import Theorems.Thm_APFB07b_realized_rate_not_forbidden
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB07b.rate_is_held_on_realized_history {Interface : Type*} {T : Type*} [Fintype T]
    {X : Type uX} {Process : Type uP} {R : Type uR}
    (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → ℝ)
    (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T) (next : T → T)
    (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (hundo : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (sigma t)))
    (i : Interface) (profile : X → Process → Prop) (now : X → R) (D : X → X) (o : T → X)
    (hrec : ∀ t : T, realized i t = now (o t)) (ho : ∀ t : T, o (next t) = D (o t))
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r))
    (t : T) (hmove : realized i (next (next t)) ≠ realized i t) :
    now (o (sigma (next t))) = now (o (next t)) ∧
      APFB01.physicalClass profile (o (sigma (next t))) ≠
        APFB01.physicalClass profile (o (next t)) := by sorry
