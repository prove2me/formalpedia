-- Prove2me | Theorems.Thm_Eidos_Examples_Reserve_withdrawal_bounded
-- name    : Eidos.Examples.Reserve.withdrawal_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:53.294956+00:00
-- url     : https://prove2.me/theorems/83685970-6fe2-4221-a725-353f307e9995
-- title:
--   Reserve: withdrawal bounded
-- statement:
--   Every accepted context obeys the withdrawal bound, for every representable reserve.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L36-L39
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L36-L39

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo

theorem Eidos.Examples.Reserve.withdrawal_bounded (reserve : Long) (ctx : Context)
    (accepted : Accepts (script reserve) ctx) : WithdrawalBounded reserve ctx := by sorry
