-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_upper_graphs
-- name    : DerivativeChainPrivate.sixth_octic_upper_graphs
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:36:41.607253+00:00
-- url     : https://prove2.me/theorems/0feebd03-d7a6-48fe-8af2-6ec2444a9bbc
-- title:
--   Both exact parameter inverse branches for row 8
-- statement:
--   Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. If $\Re z>0$, $(\Re z)^2\ge4$, $S_8(\beta,z)=0$, then $\beta/z$ is either the selected slow inverse $\alpha_8z^2-b_8+E_8(z)/z$, or the exact opposite-radical fast inverse with complementary correction specified in the formal statement.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticGraphs.lean, lines 6-76, SHA-256 1bd8976098883a5ac533d5e0eb21f1e6028ad8ad4c857f3c47cb01d0760167c5.

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

theorem DerivativeChainPrivate.sixth_octic_upper_graphs (β z : ℂ) (hx : 0<z.re) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z ∨
    β/z=(((91+3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55+27*Real.sqrt 429/4840:ℝ):ℂ)+
      ((1071/9680)*z/(z^2-17/33)-sixthOcticRemainder z)/z := by sorry
