-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_extend_prefix_six
-- name    : DerivativeChainContinuation.normalized_sixth_extend_prefix_six
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:14:01.687014+00:00
-- url     : https://prove2.me/theorems/12f3603f-4dda-4fbc-b394-aa77aa7d8eca
-- title:
--   Extend every original vertex to an actual 7-row prefix
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Fix $\Re\beta\ge0$, $\Im\beta>0$ and an existing $f:\operatorname{Fin}6\to\mathbb C$ satisfying all actual row equations, starting at zero, with both coordinates nondecreasing. The incoming sixth vertex has positive imaginary part, squared real part greater than $7/2$, and the selected sextic inverse with a finite measure of the specified support and transform. There is $z:\operatorname{Fin}7\to\mathbb C$ with $z_i=f_i$ for every original index, all 7 actual row equations, zero start and both coordinates nondecreasing. Its last vertex has positive imaginary part and squared real part greater than $4$. The last vertex has $\beta/z_6=\alpha_7z_6^2-b_7+E_7(z_6)/z_6$, $A\le39/2000$, $B\le0$, $C\le39/1000$, and wedge $(\Re z_6)^2-3(\Im z_6)^2\ge4$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthPrefixSeven.lean, lines 8-88, SHA-256 381348cfe7fbbc0f8023a25a05e09ec43924c3d627707ace1ec6ee2de6541edb.

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

theorem DerivativeChainContinuation.normalized_sixth_extend_prefix_six (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ,t∈Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0<u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
      TeschlQM.Herglotz.borelTransform μ u)
    (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) (f : Fin 6 → ℂ)
    (hfroot : ∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f i)=0)
    (hf0 : f 0=0) (hfr : Monotone (fun i => (f i).re)) (hfi : Monotone (fun i => (f i).im))
    (hfim : 0<(f 5).im) (hfX : 7/2<(f 5).re^2)
    (hfinv : β/f 5=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*(f 5)^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ,((f 5)^2-(t:ℂ))⁻¹ ∂μ)) :
    ∃ z : Fin 7 → ℂ,
      (∀ i : Fin 6,z i.castSucc=f i) ∧
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 6).im ∧ 4<(z 6).re^2 ∧
      β/z 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(z 6)^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (z 6)/z 6 ∧
      (sixthSepticRemainder (z 6)).re/(z 6).re≤39/2000 ∧
      (sixthSepticRemainder (z 6)).im/(z 6).im≤0 ∧
      (3*((sixthSepticRemainder (z 6)).re/(z 6).re)-(sixthSepticRemainder (z 6)).im/(z 6).im)/2≤39/1000 ∧
      4≤(z 6).re^2-3*(z 6).im^2 := by sorry
