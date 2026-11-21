-- Prove2me | Theorems.Thm_Eidos_Examples_Reserve_vulnerable_counterexample
-- name    : Eidos.Examples.Reserve.vulnerable_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:53.828687+00:00
-- url     : https://prove2.me/theorems/03b65062-b0b2-458f-b46e-745a061783e7
-- title:
--   Reserve: vulnerable counterexample
-- statement:
--   The unsafe rule accepts an 80 ERG decrease despite a 70 ERG bound.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L60-L65
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean#L60-L65

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo

theorem Eidos.Examples.Reserve.vulnerable_counterexample :
    Accepts vulnerableScript attackContext ∧
      ¬ WithdrawalBounded exampleReserve attackContext := by sorry
