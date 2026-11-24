-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_thetaE1Word_eq
-- name    : DyckAlgebra.DyckRepU.thetaE1Word_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:36.067974+00:00
-- url     : https://prove2.me/theorems/f6729627-8c3e-4100-97ec-dd8836412e99
-- title:
--   Dyck Rep U: theta E1 Word eq
-- statement:
--   **Explicit `Θ`--`e₁` commutation relation at level zero.**  Here `(Q2)`
--   has coefficient `-1`.  The correction is the positive `D` series with its
--   `D₁` term removed, matching
--   `[Θ,e₁] = ∑_{n≥2} u^(n-1) Dₙ · Θ` after introducing the intertwiner.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L91-L118
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L91-L118

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.thetaE1Word_eq (hlevel : ρ.level = 0) :
    ρ.thetaE1Word = ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord) := by sorry
