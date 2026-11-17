-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_quarter_relative_turn_halves_the_count
-- name    : APFPaper5.K3.Carrying.quarter_relative_turn_halves_the_count
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:29:58.753697+00:00
-- url     : https://prove2.me/theorems/9a805e17-c748-4bdc-87e6-6c5f5ab74d72
-- title:
--   quarter relative turn halves the count
-- statement:
--   Result: quarter relative turn halves the count. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem quarter_relative_turn_halves_the_count (u : ℝ × ℝ) (hu : u.1 * u.1 + u.2 * u.2 = 1) :
--       meet (turnBy 0 1 u) u = meet u u / 2
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:206; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem APFPaper5.K3.Carrying.quarter_relative_turn_halves_the_count :
∀ (u : Prod.{0, 0} Real Real)
  (hu :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.fst.{0, 0} Real Real u)
          (@Prod.fst.{0, 0} Real Real u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.snd.{0, 0} Real Real u)
          (@Prod.snd.{0, 0} Real Real u)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Eq.{1} Real
    (APFPaper5.K3.Carrying.meet
      (APFPaper5.K3.Carrying.turnBy (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
      u)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (APFPaper5.K3.Carrying.meet u u)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) := by sorry
