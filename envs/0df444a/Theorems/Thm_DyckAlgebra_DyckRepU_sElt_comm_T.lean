-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_sElt_comm_T
-- name    : DyckAlgebra.DyckRepU.sElt_comm_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:53.728251+00:00
-- url     : https://prove2.me/theorems/eadb1b98-b880-4628-a79d-2bae01143726
-- title:
--   Dyck Rep U: s Elt comm T
-- statement:
--   The Dyck Rep U construction uses the s Elt comm T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L292-L297
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L292-L297

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.sElt_comm_T (j : ℕ) (hj : 2 ≤ j) : ρ.sElt * ρ.T j = ρ.T j * ρ.sElt := by sorry
