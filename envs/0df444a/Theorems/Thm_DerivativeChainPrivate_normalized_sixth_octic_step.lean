-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_octic_step
-- name    : DerivativeChainPrivate.normalized_sixth_octic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:13:20.123787+00:00
-- url     : https://prove2.me/theorems/7910d0a0-899c-4f53-a9fe-bcbf130ab045
-- title:
--   A selected fixed-parameter seventh-to-eighth row step
-- statement:
--   Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. Assume $\Re\beta\ge0$, $\Im\beta>0$, $\Re w,\Im w>0$, $(\Re w)^2\ge4$, $S_7(\beta,w)=0$ and $\beta/w=\alpha_7w^2-b_7+E_7(w)/w$. There exists $z$ northeast of $w$ with $S_8(\beta,z)=0$ and $\beta/z=\alpha_8z^2-b_8+E_8(z)/z$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticStep.lean, lines 8-84, SHA-256 03960566709f32ea1dca17cc77038a524661cda82d158aa050a148984e309544.

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

theorem DerivativeChainPrivate.normalized_sixth_octic_step (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 4≤w.re^2)
    (hwroot : (1360/13)*β^2*w-35*β*w^4+85*β*w^2-(1445/78)*β+
      w^7-7*w^5+(595/48)*w^3-(1445/312)*w=0)
    (hwinv : β/w=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*w^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder w/w) :
    ∃ z : ℂ,
      (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
        z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧
      β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z := by sorry
