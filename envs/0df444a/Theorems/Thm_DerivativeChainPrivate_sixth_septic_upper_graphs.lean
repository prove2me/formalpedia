-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_upper_graphs
-- name    : DerivativeChainPrivate.sixth_septic_upper_graphs
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:12:52.51318+00:00
-- url     : https://prove2.me/theorems/c160e711-bf90-4e5b-b118-63f1ca75b8cc
-- title:
--   Both exact parameter inverse branches for row 7
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. If $\Re z>0$, $(\Re z)^2\ge7/2$, $S_7(\beta,z)=0$, then $\beta/z$ is either the selected slow inverse $\alpha_7z^2-b_7+E_7(z)/z$, or the exact opposite-radical fast inverse with complementary correction specified in the formal statement.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticGraphs.lean, lines 6-75, SHA-256 2b1cce30a7f1ec4b31bddbae6b861ee79b8487004ee40a8ebf456ff4d02deed9.

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

theorem DerivativeChainPrivate.sixth_septic_upper_graphs (β z : ℂ) (hx : 0<z.re) (hX : 7/2≤z.re^2)
    (hroot : (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
      z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0) :
    β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z ∨
    β/z=(((455+3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32+77*Real.sqrt 15145/37280:ℝ):ℂ)+((17/96)/z-sixthSepticRemainder z)/z := by sorry
