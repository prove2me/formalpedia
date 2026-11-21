-- Prove2me | Theorems.Thm_Eidos_Examples_Reserve_checked_withdrawal
-- name    : Eidos.Examples.Reserve.checked_withdrawal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:56.763518+00:00
-- url     : https://prove2.me/theorems/51023a1b-eef9-4561-9d0b-14260332eca9
-- title:
--   Reserve: checked withdrawal
-- statement:
--   For a nonnegative reserve, actual checked Long subtraction also succeeds.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L42-L50
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L42-L50

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo

theorem Eidos.Examples.Reserve.checked_withdrawal (reserve : Long) (ctx : Context)
    (nonnegative : 0 ≤ reserve.val) (accepted : Accepts (script reserve) ctx) :
    ∃ out amount, ctx.outputs[0]? = some out ∧
      Long.sub ctx.self.value out.value = .ok amount ∧
      0 ≤ amount.val ∧ amount.val ≤ ctx.self.value.val - reserve.val := by sorry
