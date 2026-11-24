-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_thetaDOneWord_eq_series
-- name    : DyckAlgebra.DyckRepU.thetaDOneWord_eq_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:52.253845+00:00
-- url     : https://prove2.me/theorems/4e7cb696-31f0-4f3d-8fa2-ce6f286d8517
-- title:
--   Dyck Rep U: theta DOne Word eq series
-- statement:
--   **Explicit `Θ`--`D₁` commutation relation.**  The transform of `D₁` is
--   the complete positive `D` generating series.  This is the finite inverse form
--   of `Θ D₁ = (∑_{n≥1} u^(n-1) Dₙ) Θ` before adjoining an external intertwiner.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L80-L85
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L80-L85

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.thetaDOneWord_eq_series : ρ.thetaDOneWord = ρ.dPositiveSeries := by sorry
