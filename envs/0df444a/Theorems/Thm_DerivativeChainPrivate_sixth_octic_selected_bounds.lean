-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_selected_bounds
-- name    : DerivativeChainPrivate.sixth_octic_selected_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:03:13.679953+00:00
-- url     : https://prove2.me/theorems/d4980f4e-fbdc-44d3-9489-40e125a6925a
-- title:
--   Strict eighth-row localization and selected correction bounds
-- statement:
--   Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. If $\Re\beta\ge0$, $\Re z,\Im z>0$, $(\Re z)^2\ge4$, and $\beta/z=\alpha_8z^2-b_8+E_8(z)/z$, then $(\Re z)^2>26/5$, $A\le9/1000$, $B\le0$, $C\le73/4000$, and $(\Re z)^2-3(\Im z)^2\ge26/5$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticBounds.lean, lines 7-38, SHA-256 a5bbd83b5a6239ee1e1d15b9c295df2deb2042c5090c436b3185cbfe03e7c5dc.

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

theorem DerivativeChainPrivate.sixth_octic_selected_bounds (β z : ℂ) (hR : 0≤β.re) (hx : 0<z.re) (hy : 0<z.im)
    (hX : 4≤z.re^2)
    (hg : β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z) :
    26/5<z.re^2 ∧ (sixthOcticRemainder z).re/z.re≤9/1000 ∧
      (sixthOcticRemainder z).im/z.im≤0 ∧
      (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤73/4000 ∧
      26/5≤z.re^2-3*z.im^2 := by sorry
