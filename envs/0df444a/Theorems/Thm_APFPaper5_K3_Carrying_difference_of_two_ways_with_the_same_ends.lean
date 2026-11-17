-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_difference_of_two_ways_with_the_same_ends
-- name    : APFPaper5.K3.Carrying.difference_of_two_ways_with_the_same_ends
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:29:34.449645+00:00
-- url     : https://prove2.me/theorems/8770a776-1d68-4021-88b8-6db1f722ccaa
-- title:
--   difference of two ways with the same ends
-- statement:
--   Result: difference of two ways with the same ends. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem difference_of_two_ways_with_the_same_ends (g : X → ℝ) (A : X → X → ℝ) (p q : ℕ → X)
--       (n m : ℕ) (hstart : p 0 = q 0) (hend : p n = q m) :
--       total (represent g A) p n - total (represent g A) q m = total A p n - total A q m
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:156; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.difference_of_two_ways_with_the_same_ends :
∀ {X : Type apfNative_u} (g : X → Real) (A : X → X → Real) (p q : Nat → X) (n m : Nat)
  (hstart :
    @Eq.{apfNative_u + 1} X (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (hend : @Eq.{apfNative_u + 1} X (p n) (q m)),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@APFPaper5.K3.Carrying.total.{apfNative_u} X (@APFPaper5.K3.Carrying.represent.{apfNative_u} X g A) p n)
      (@APFPaper5.K3.Carrying.total.{apfNative_u} X (@APFPaper5.K3.Carrying.represent.{apfNative_u} X g A) q m))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@APFPaper5.K3.Carrying.total.{apfNative_u} X A p n) (@APFPaper5.K3.Carrying.total.{apfNative_u} X A q m)) := by sorry
