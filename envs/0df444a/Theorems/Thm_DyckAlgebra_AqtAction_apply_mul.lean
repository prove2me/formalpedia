-- Prove2me | Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
-- name    : DyckAlgebra.AqtAction.apply_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:51:39.752984+00:00
-- url     : https://prove2.me/theorems/f8750d4f-1c5e-4dbd-aedf-b143b403452c
-- title:
--   Aqt Action: apply mul
-- statement:
--   The Aqt Action construction uses the apply mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Rep.lean#L56-L58
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Rep.lean#L56-L58

import Definitions.Def_RequestProject_Aqt_Algebra
import Definitions.Def_RequestProject_Aqt_Rep
set_option autoImplicit true
open DyckAlgebra
universe v
attribute [instance] AqtAction.addCommGroup AqtAction.module
open DyckAlgebra.AqtAction
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t)

theorem DyckAlgebra.AqtAction.apply_mul (a b : Aqt q t) (v : ρ.carrier) :
    ρ.apply (a * b) v = ρ.apply a (ρ.apply b v) := by sorry
