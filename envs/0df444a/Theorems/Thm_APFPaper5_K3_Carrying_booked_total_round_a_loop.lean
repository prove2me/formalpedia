-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_booked_total_round_a_loop
-- name    : APFPaper5.K3.Carrying.booked_total_round_a_loop
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:29:21.984117+00:00
-- url     : https://prove2.me/theorems/488ae9a1-ceb0-4bed-9e61-1c14d7613fd6
-- title:
--   booked total round a loop
-- statement:
--   Result: booked total round a loop. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem booked_total_round_a_loop (E : X → ℝ) (p : ℕ → X) (n : ℕ) (hloop : p n = p 0) :
--       total (fun x y => E y - E x) p n = 0
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:97; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.booked_total_round_a_loop :
∀ {X : Type apfNative_u} (E : X → Real) (p : Nat → X) (n : Nat)
  (hloop : @Eq.{apfNative_u + 1} X (p n) (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  @Eq.{1} Real
    (@APFPaper5.K3.Carrying.total.{apfNative_u} X
      (fun (x y : X) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (E y) (E x)) p n)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by sorry
