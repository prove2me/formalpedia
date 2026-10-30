-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_octic_inverse_exact
-- name    : DerivativeChainPrivate.sixth_octic_inverse_exact
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:34:26.116632+00:00
-- url     : https://prove2.me/theorems/6603e1f8-7289-4b3e-ba92-a0000f5a6262
-- title:
--   The exact selected eighth-row slow radical inverse
-- statement:
--   Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For $z\ne0$, $|z^{-1}|^2\le1/4$, $\alpha_8z^2-b_8+E_8(z)/z=[(91/1360)z^4-(13/48)z^2+17/96-(3\sqrt{429}/1360)z^4\sqrt{R_8(z^{-2})}]/(z^2-17/33)$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticInverse.lean, lines 53-75, SHA-256 bb1281ac3a64a3fca6d850aca2c032e1eb0ae222c510b2e236ab5da8c0069a3c.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
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

theorem DerivativeChainPrivate.sixth_octic_inverse_exact (z : ℂ) (hz : z≠0) (hn : ‖z⁻¹‖^2≤1/4) :
    (((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z=
      ((91/1360)*z^4-(13/48)*z^2+17/96-
        ((3*Real.sqrt 429/1360:ℝ):ℂ)*z^4*Complex.sqrt (sixthOcticRadicand ((z⁻¹)^2)))/(z^2-17/33) := by sorry
