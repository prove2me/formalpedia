-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_data
-- name    : DerivativeChainPrivate.sixth_octic_upper_data
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:06:56.186102+00:00
-- url     : https://prove2.me/theorems/3c9b6035-3581-4429-adf4-0575e414a571
-- title:
--   Controlled upper-half-plane data for both row-8 inverse branches
-- statement:
--   Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. For any $S_8(\beta,z)=0$ with positive coordinates and $(\Re z)^2\ge4$, there are real $\alpha,b$ and complex $E$ such that $\alpha>1/50$, $\beta/z=\alpha z^2-b+E/z$, and $\Im(\beta/z)>0$. Either $\alpha,b,E$ are exactly the slow coefficients and $E_8(z)$, with $C\ge0$, or they are the exact fast coefficients and complementary correction with $0\le A\le1/20$, $-1/20\le B\le0$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticUpperData.lean, lines 8-53, SHA-256 a9c588aabe7f99863a736838743d04e2c8e616ce9e5d161af6c7be3a53f84fc5.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
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

theorem DerivativeChainPrivate.sixth_octic_upper_data (β z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    ∃ α b : ℝ,∃ e : ℂ, 1/50<α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0<(β/z).im ∧
      ((α=(91-3*Real.sqrt 429)/1360 ∧ b=13/55-27*Real.sqrt 429/4840 ∧
          e=sixthOcticRemainder z ∧ 0≤(3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α=(91+3*Real.sqrt 429)/1360 ∧ b=13/55+27*Real.sqrt 429/4840 ∧
          0≤e.re/z.re ∧ e.re/z.re≤1/20 ∧ -(1/20)≤e.im/z.im ∧ e.im/z.im≤0)) := by sorry
