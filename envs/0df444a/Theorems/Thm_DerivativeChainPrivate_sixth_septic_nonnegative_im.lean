-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_nonnegative_im
-- name    : DerivativeChainPrivate.sixth_septic_nonnegative_im
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:06:03.61875+00:00
-- url     : https://prove2.me/theorems/2d8e656e-0033-43e8-b4d7-2ac0e85bdfe1
-- title:
--   The parameter quadrant determines row-7 root phase
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. If $\Re\beta,\Im\beta\ge0$, $\Re z>0$, $(\Re z)^2\ge7/2$ and $S_7(\beta,z)=0$, then $\Im z\ge0$ and $\Im\beta=0$ if and only if $\Im z=0$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticPhase.lean, lines 5-57, SHA-256 01d3ee262f7e06efd31311ea2272904e8d516344bbdcc6ce1f1fa5ea37ce9542.

import Mathlib
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

theorem DerivativeChainPrivate.sixth_septic_nonnegative_im (β z : ℂ) (hR : 0≤β.re) (hI : 0≤β.im)
    (hx : 0<z.re) (hX : 7/2≤z.re^2)
    (hroot : (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
      z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0) :
    0≤z.im ∧ (β.im=0 ↔ z.im=0) := by sorry
