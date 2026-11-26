-- Prove2me | Theorems.Thm_AME125_certOK_sum
-- name    : AME125.certOK_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:29.051488+00:00
-- url     : https://prove2.me/theorems/5022b0c0-1bd1-4cff-856e-b9419fb1437b
-- title:
--   AME125: cert OK sum
-- statement:
--   A passed certificate check, as an identity in `ZMod 5`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L122-L137
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L122-L137

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.certOK_sum {c : ℕ × List ℕ} (hc : certOK c = true) (i k : Fin 12)
    (hi : c.1.testBit i.1 = true) (hk : c.1.testBit k.1 = true) :
    ∑ j : Fin 12, (if c.1.testBit j.1 then 0 else theta i j * (certN c.1 c.2 j k : ZMod 5)) =
      if i = k then 1 else 0 := by sorry
