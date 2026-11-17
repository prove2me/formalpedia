-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_booked_steps_round_a_loop_are_free
-- name    : APFPaper5.K3.Carrying.booked_steps_round_a_loop_are_free
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:26:27.307963+00:00
-- url     : https://prove2.me/theorems/b5ce5791-6d4f-403a-843a-fe0b8f60c3e2
-- title:
--   booked steps round a loop are free
-- statement:
--   Result: booked steps round a loop are free. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem booked_steps_round_a_loop_are_free (E : X → ℝ) (p : ℕ → X) (n : ℕ)
--       (hstep : ∀ i, i < n → E (p i) ≤ E (p (i + 1))) (hloop : p n = p 0) :
--       ∀ i, i < n → E (p (i + 1)) - E (p i) = 0
--   ```
--
--   Module context and limits: A supplied difference-of-state-function charge telescopes and vanishes on loops. Every loop step vanishes only with the explicit nondecreasing-state-function hypothesis. Endpoint changes of presentation preserve closed totals and relative path charges; distinct-endpoint open totals can be gauged to zero. Squared-sum interference is a supplied rule, not a derived physical gauge law.
--
--   Source scope parameters:
--
--   ```lean
--   universe u
--   variable {X : Type u}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:113; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.booked_steps_round_a_loop_are_free :
∀ {X : Type apfNative_u} (E : X → Real) (p : Nat → X) (n : Nat)
  (hstep :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Real Real.instLE (E (p i))
          (E
            (p
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  (hloop : @Eq.{apfNative_u + 1} X (p n) (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (i : Nat),
  @LT.lt.{0} Nat instLTNat i n →
    @Eq.{1} Real
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (E
          (p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (E (p i)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by sorry
