-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_yy_comm_Tinv
-- name    : DyckAlgebra.DyckRepU.yy_comm_Tinv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:34.674806+00:00
-- url     : https://prove2.me/theorems/9f57e3a7-059a-4fd1-a69c-0f2107d6f89c
-- title:
--   Dyck Rep U: yy comm Tinv
-- statement:
--   The Dyck Rep U construction uses the yy comm Tinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L364-L373
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L364-L373

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.yy_comm_Tinv (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.yy i * ρ.Tinv j = ρ.Tinv j * ρ.yy i := by sorry
