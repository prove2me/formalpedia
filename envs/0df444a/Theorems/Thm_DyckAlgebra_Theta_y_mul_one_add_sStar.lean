-- Prove2me | Theorems.Thm_DyckAlgebra_Theta_y_mul_one_add_sStar
-- name    : DyckAlgebra.Theta.y_mul_one_add_sStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:40.015811+00:00
-- url     : https://prove2.me/theorems/543f05ac-103d-4901-813e-1f2a9ae49119
-- title:
--   Theta: y mul one add s Star
-- statement:
--   First identity in `lem:theta_q2` of the source.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L39-L46
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L39-L46

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.Theta
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem DyckAlgebra.Theta.y_mul_one_add_sStar (u : 𝕜) (w y z : A)
    (hwL : (1 + u • y) * w = 1) (hyz : y * z = z * y) :
    y * (1 + sStar u y z) = (1 + u • y) * (1 - s u w y z) * y := by sorry
