-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_nonnegative_im
-- name    : DerivativeChainPrivate.sixth_octic_nonnegative_im
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:11:11.487669+00:00
-- url     : https://prove2.me/theorems/92134a08-a533-4081-a8b3-575384735fe6
-- title:
--   The parameter quadrant determines row-8 root phase
-- statement:
--   Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. If $\Re\beta,\Im\beta\ge0$, $\Re z>0$, $(\Re z)^2\ge4$ and $S_8(\beta,z)=0$, then $\Im z\ge0$ and $\Im\beta=0$ if and only if $\Im z=0$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticPhase.lean, lines 5-57, SHA-256 000e18acae938f7f57432fb209a945f002bdbd8e4943c3337c057bd7eefb8e78.

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

theorem DerivativeChainPrivate.sixth_octic_nonnegative_im (β z : ℂ) (hR : 0≤β.re) (hI : 0≤β.im)
    (hx : 0<z.re) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    0≤z.im ∧ (β.im=0 ↔ z.im=0) := by sorry
