-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_represented_total
-- name    : APFPaper5.K3.Carrying.represented_total
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:30:20.15365+00:00
-- url     : https://prove2.me/theorems/474e47cc-d3a9-4530-8eb5-7f7e64188753
-- title:
--   represented total
-- statement:
--   Result: represented total. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem represented_total (g : X → ℝ) (A : X → X → ℝ) (p : ℕ → X) (n : ℕ) :
--       total (represent g A) p n = total A p n + g (p n) - g (p 0)
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:129; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.represented_total :
∀ {X : Type apfNative_u} (g : X → Real) (A : X → X → Real) (p : Nat → X) (n : Nat),
  @Eq.{1} Real (@APFPaper5.K3.Carrying.total.{apfNative_u} X (@APFPaper5.K3.Carrying.represent.{apfNative_u} X g A) p n)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K3.Carrying.total.{apfNative_u} X A p n) (g (p n)))
      (g (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by sorry
