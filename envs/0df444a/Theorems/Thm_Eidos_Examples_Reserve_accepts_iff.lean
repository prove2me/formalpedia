-- Prove2me | Theorems.Thm_Eidos_Examples_Reserve_accepts_iff
-- name    : Eidos.Examples.Reserve.accepts_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:52.531612+00:00
-- url     : https://prove2.me/theorems/20f02aa8-67f4-4ae9-b8b9-e4aa8ff88a7a
-- title:
--   Reserve: accepts iff
-- statement:
--   Exact characterization, including the requirement that OUTPUTS(0) exists.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L21-L33
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L21-L33

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo

theorem Eidos.Examples.Reserve.accepts_iff (reserve : Long) (ctx : Context) :
    Accepts (script reserve) ctx ↔
      ∃ out, ctx.outputs[0]? = some out ∧
        out.value.val ≤ ctx.self.value.val ∧ reserve.val ≤ out.value.val := by sorry
