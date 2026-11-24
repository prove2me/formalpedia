-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_vbarSum_eq_bval
-- name    : FairSelling.ZeroPrice.vbarSum_eq_bval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:55:18.763487+00:00
-- url     : https://prove2.me/theorems/d57c6889-f0f4-4abf-b4aa-865e7bf2be0d
-- title:
--   Zero Price: vbar Sum eq bval
-- statement:
--   With zero prices the modified valuation `v̄` is the valuation itself.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L105-L108
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L105-L108

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.ZeroPrice.vbarSum_eq_bval (w p : G → ℝ) (hp0 : ∀ g, p g = 0) (hw : ∀ g, 0 ≤ w g) (S : Finset G) :
    vbarSum w p S = bval w S := by sorry
