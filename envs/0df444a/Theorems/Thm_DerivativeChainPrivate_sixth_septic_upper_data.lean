-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_septic_upper_data
-- name    : DerivativeChainPrivate.sixth_septic_upper_data
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:03:04.385991+00:00
-- url     : https://prove2.me/theorems/8453e74d-261f-4b6f-9e0d-b1cdc784aa01
-- title:
--   Controlled upper-half-plane data for both row-7 inverse branches
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. For any $S_7(\beta,z)=0$ with positive coordinates and $(\Re z)^2\ge7/2$, there are real $\alpha,b$ and complex $E$ such that $\alpha>3/100$, $\beta/z=\alpha z^2-b+E/z$, and $\Im(\beta/z)>0$. Either $\alpha,b,E$ are exactly the slow coefficients and $E_7(z)$, with $C\ge0$, or they are the exact fast coefficients and complementary correction with $0\le A\le1/18$, $-1/18\le B\le0$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticUpperData.lean, lines 7-63, SHA-256 73a32cca9fae8ea9daa964ab5c243858bbd2e4672b2fe9a07bee26ab49a8b9eb.

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

theorem DerivativeChainPrivate.sixth_septic_upper_data (β z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 7/2≤z.re^2)
    (hroot : (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
      z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0) :
    ∃ α b : ℝ,∃ e : ℂ, 3/100<α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0<(β/z).im ∧
      ((α=(455-3*Real.sqrt 15145)/2720 ∧ b=13/32-77*Real.sqrt 15145/37280 ∧
          e=sixthSepticRemainder z ∧ 0≤(3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α=(455+3*Real.sqrt 15145)/2720 ∧ b=13/32+77*Real.sqrt 15145/37280 ∧
          0≤e.re/z.re ∧ e.re/z.re≤1/18 ∧ -(1/18)≤e.im/z.im ∧ e.im/z.im≤0)) := by sorry
