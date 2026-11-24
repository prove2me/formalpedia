-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_preserve_I1_via_sStar
-- name    : DyckAlgebra.DyckRepU.theta_preserve_I1_via_sStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:11.500403+00:00
-- url     : https://prove2.me/theorems/12fece75-7448-4573-9a70-25215bbf7271
-- title:
--   Dyck Rep U: theta preserve I1 via s Star
-- statement:
--   **`Θ` preserves the relation (I1) at an arbitrary level `k`** — the general case,
--   keeping the `(d_+^*)^k` factor.
--
--   Given that `s^*` annihilates every `(d_+^*)^j ε₀` (`j ≥ 1`) and the level-`k`
--   relation `(d_- d_+^* - 1)(d_+^*)^k ε₀ = 0`, the `Θ`-image
--   `(d_- Θ(d_+^*) - 1) (Θ(d_+^*))^k ε₀` is again `0`.
--
--   The proof uses only `theta_dps_pow_eq`: since `Θ(d_+^*)^k ε₀ = (d_+^*)^k ε₀` (and
--   likewise at `k+1`), the `Θ`-image operator lands on the original level-`k`
--   relation.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L129-L142
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L129-L142

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_preserve_I1_via_sStar (k : ℕ) (e0 : ρ.carrier)
    (hsStar : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI1 : (ρ.dm * ρ.dps - 1) * ρ.dps ^ k * e0 = 0) :
    (ρ.dm * ρ.Θdps - 1) * ρ.Θdps ^ k * e0 = 0 := by sorry
