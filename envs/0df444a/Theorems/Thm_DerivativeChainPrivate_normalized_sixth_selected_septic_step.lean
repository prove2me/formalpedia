-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_selected_septic_step
-- name    : DerivativeChainPrivate.normalized_sixth_selected_septic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:11:45.732736+00:00
-- url     : https://prove2.me/theorems/bf35aee9-4425-4262-aa8f-a9c84ca36bc3
-- title:
--   A seventh-row step with all selected same-point bounds
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. Let $H(u)=u^2-(85/43)u+1445/1806+(24565/211302)/u$. Let $\mu$ be a finite positive measure supported almost everywhere on $[-1/4,3/2]$, representing $\operatorname{sexticShift}(-85/43,1445/1806,24565/211302;u)$ as $\int(t-u)^{-1}\,d\mu(t)$ for every $\Im u>0$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Assume $\Re\beta\ge0$, $\Im\beta>0$, $\Re w,\Im w>0$, $(\Re w)^2\ge7/2$, $S_6(\beta,w)=0$, and its selected sextic measure inverse at $w$. There is $z$ northeast of $w$ with $S_7(\beta,z)=0$, $\Im z>0$, $(\Re z)^2>4$, the selected seventh-row inverse, $A\le39/2000$, $B\le0$, $C\le39/1000$, and $(\Re z)^2-3(\Im z)^2\ge4$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticBounds.lean, lines 56-91, SHA-256 51fb94d369ee1ceaa45bc4605c8d4364be80261b5113a55e2968e95466dd5786.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.normalized_sixth_selected_septic_step (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ,t∈Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0<u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
      TeschlQM.Herglotz.borelTransform μ u)
    (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 7/2≤w.re^2)
    (hwroot : (1360/91)*β^2-20*β*w^3+(170/7)*β*w+w^6-5*w^4+(85/16)*w^2-1445/2184=0)
    (hwinv : β/w=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*w^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ,(w^2-(t:ℂ))⁻¹ ∂μ)) :
    ∃ z : ℂ,
      (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
        z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧ 0<z.im ∧ 4<z.re^2 ∧
      β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z ∧
      (sixthSepticRemainder z).re/z.re≤39/2000 ∧ (sixthSepticRemainder z).im/z.im≤0 ∧
      (3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2≤39/1000 ∧
      4≤z.re^2-3*z.im^2 := by sorry
