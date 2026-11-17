-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_total_of_a_state_function
-- name    : APFPaper5.K3.Carrying.total_of_a_state_function
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:30:20.490344+00:00
-- url     : https://prove2.me/theorems/4dbc8e98-e33e-4953-9219-4fcdad62d98e
-- title:
--   total of a state function
-- statement:
--   Result: total of a state function. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem total_of_a_state_function (E : X → ℝ) (p : ℕ → X) (n : ℕ) :
--       total (fun x y => E y - E x) p n = E (p n) - E (p 0)
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:89; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.total_of_a_state_function :
∀ {X : Type apfNative_u} (E : X → Real) (p : Nat → X) (n : Nat),
  @Eq.{1} Real
    (@APFPaper5.K3.Carrying.total.{apfNative_u} X
      (fun (x y : X) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (E y) (E x)) p n)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (E (p n))
      (E (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by sorry
