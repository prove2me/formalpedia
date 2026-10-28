-- Prove2me | Theorems.Thm_BitDFT_roundPair_product_disc
-- name    : BitDFT.roundPair_product_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:36:32.628163+00:00
-- url     : https://prove2.me/theorems/26b3e454-b4be-42d5-8df9-946032d1a0cd
-- title:
--   Rounding a product of unit-disc fixed-point values preserves the unit disc
-- statement:
--   Let $U,V$ be two complex fixed-point values at precision $p$, each represented in the closed unit disc. Then rounding the product of their represented complex values coordinatewise toward zero gives another precision-$p$ value in the closed unit disc. This is the range-preservation property needed for fixed-point complex multiplication.
-- source:
--   A direct consequence of the proved rounding representation BitDFT.rounding_bridge and the fixed-point contraction bound IntMul.HvdH.rho_bounds. This separates the unit-disc postcondition from the machine-construction proof.

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_rounding_bridge
import Theorems.Thm_IntMul_HvdH_rho_bounds
set_option autoImplicit false
noncomputable section
open BitDFT

theorem BitDFT.roundPair_product_disc (p : ℕ) (U V : ℤ × ℤ) (hU : inDisc p U) (hV : inDisc p V) :
    inDisc p (roundPair p (value p U * value p V)) := by sorry
