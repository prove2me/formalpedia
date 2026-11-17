-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_loop_total_is_the_same_under_every_presentation
-- name    : APFPaper5.K3.Carrying.loop_total_is_the_same_under_every_presentation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:29:57.22517+00:00
-- url     : https://prove2.me/theorems/6e80e9dd-8d2c-449a-bf16-21f2d795327e
-- title:
--   loop total is the same under every presentation
-- statement:
--   Result: loop total is the same under every presentation. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem loop_total_is_the_same_under_every_presentation (g : X → ℝ) (A : X → X → ℝ) (p : ℕ → X)
--       (n : ℕ) (hloop : p n = p 0) : total (represent g A) p n = total A p n
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
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:139; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u

theorem APFPaper5.K3.Carrying.loop_total_is_the_same_under_every_presentation :
∀ {X : Type apfNative_u} (g : X → Real) (A : X → X → Real) (p : Nat → X) (n : Nat)
  (hloop : @Eq.{apfNative_u + 1} X (p n) (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  @Eq.{1} Real (@APFPaper5.K3.Carrying.total.{apfNative_u} X (@APFPaper5.K3.Carrying.represent.{apfNative_u} X g A) p n)
    (@APFPaper5.K3.Carrying.total.{apfNative_u} X A p n) := by sorry
