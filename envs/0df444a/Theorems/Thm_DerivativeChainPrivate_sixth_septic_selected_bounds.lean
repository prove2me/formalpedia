-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_selected_bounds
-- name    : DerivativeChainPrivate.sixth_septic_selected_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:03:07.767146+00:00
-- url     : https://prove2.me/theorems/bee4c380-fc2c-4a72-8a08-2ed42096f778
-- title:
--   Strict seventh-row localization and selected correction bounds
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. If $\Re\beta\ge0$, $\Re z,\Im z>0$, $(\Re z)^2\ge7/2$, and $\beta/z=\alpha_7z^2-b_7+E_7(z)/z$, then $(\Re z)^2>4$, $A\le39/2000$, $B\le0$, $C\le39/1000$, and $(\Re z)^2-3(\Im z)^2\ge4$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticBounds.lean, lines 8-54, SHA-256 51fb94d369ee1ceaa45bc4605c8d4364be80261b5113a55e2968e95466dd5786.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.sixth_septic_selected_bounds (β z : ℂ) (hR : 0≤β.re) (hx : 0<z.re) (hy : 0<z.im)
    (hX : 7/2≤z.re^2)
    (hg : β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z) :
    4<z.re^2 ∧ (sixthSepticRemainder z).re/z.re≤39/2000 ∧
      (sixthSepticRemainder z).im/z.im≤0 ∧
      (3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2≤39/1000 ∧
      4≤z.re^2-3*z.im^2 := by sorry
