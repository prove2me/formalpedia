-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_septic_step
-- name    : DerivativeChainPrivate.normalized_sixth_septic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:09:05.275166+00:00
-- url     : https://prove2.me/theorems/2dc73352-ecec-43b1-9a27-431416614b73
-- title:
--   A selected fixed-parameter sixth-to-seventh row step
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Assume $\Re\beta\ge0$, $\Im\beta>0$, $\Re w,\Im w>0$, $(\Re w)^2\ge7/2$, $S_6(\beta,w)=0$ and $\beta/w=\alpha_6w^2-b_6+E_0/w$. If $A_0\le29/1600$, $B_0\le0$, $C_0\le1/20$, there is $z$ northeast of $w$ with $S_7(\beta,z)=0$ and $\beta/z=\alpha_7z^2-b_7+E_7(z)/z$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticStep.lean, lines 7-86, SHA-256 a2e49f6d2ad625e5a3875d92525e0576a26b231b3f70075965f15caa5b99dbbd.

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

theorem DerivativeChainPrivate.normalized_sixth_septic_step (β w E₀ : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 7/2≤w.re^2)
    (hwroot : (1360/91)*β^2-20*β*w^3+(170/7)*β*w+w^6-5*w^4+(85/16)*w^2-1445/2184=0)
    (hwinv : β/w=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*w^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+E₀/w)
    (hA₀hi : E₀.re/w.re≤29/1600) (hB₀hi : E₀.im/w.im≤0)
    (hC₀hi : (3*(E₀.re/w.re)-E₀.im/w.im)/2≤1/20) :
    ∃ z : ℂ,
      (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
        z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧
      β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z := by sorry
