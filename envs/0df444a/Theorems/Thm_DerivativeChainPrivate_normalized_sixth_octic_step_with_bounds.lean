-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_octic_step_with_bounds
-- name    : DerivativeChainPrivate.normalized_sixth_octic_step_with_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:16:58.069442+00:00
-- url     : https://prove2.me/theorems/5332ce2d-4d21-4608-afb1-fdf4b667d008
-- title:
--   An eighth-row step with all selected same-point bounds
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Assume $\Re\beta\ge0$, $\Im\beta>0$, $\Re w,\Im w>0$, $(\Re w)^2\ge4$, $S_7(\beta,w)=0$ and its exact selected seventh-row inverse. There exists $z$ northeast of $w$ with $S_8(\beta,z)=0$, $\Im z>0$, $(\Re z)^2>26/5$, the selected eighth-row inverse, $A\le9/1000$, $B\le0$, $C\le73/4000$, and $(\Re z)^2-3(\Im z)^2\ge26/5$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticBounds.lean, lines 40-60, SHA-256 a5bbd83b5a6239ee1e1d15b9c295df2deb2042c5090c436b3185cbfe03e7c5dc.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
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

theorem DerivativeChainPrivate.normalized_sixth_octic_step_with_bounds (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 4≤w.re^2)
    (hwroot : (1360/13)*β^2*w-35*β*w^4+85*β*w^2-(1445/78)*β+
      w^7-7*w^5+(595/48)*w^3-(1445/312)*w=0)
    (hwinv : β/w=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*w^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder w/w) :
    ∃ z : ℂ,
      (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
        z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧ 0<z.im ∧ 26/5<z.re^2 ∧
      β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z ∧
      (sixthOcticRemainder z).re/z.re≤9/1000 ∧ (sixthOcticRemainder z).im/z.im≤0 ∧
      (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤73/4000 ∧
      26/5≤z.re^2-3*z.im^2 := by sorry
