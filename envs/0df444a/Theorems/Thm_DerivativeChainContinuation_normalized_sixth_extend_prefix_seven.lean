-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_extend_prefix_seven
-- name    : DerivativeChainContinuation.normalized_sixth_extend_prefix_seven
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:18:52.299925+00:00
-- url     : https://prove2.me/theorems/7738e78d-dbe1-44ae-9e94-5fbeb50f0c93
-- title:
--   Extend every original vertex to an actual 8-row prefix
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Fix $\Re\beta\ge0$, $\Im\beta>0$ and an existing $f:\operatorname{Fin}7\to\mathbb C$ satisfying all actual row equations, starting at zero, with both coordinates nondecreasing. The incoming seventh vertex has positive imaginary part, squared real part greater than $4$, and its exact selected seventh-row inverse. There is $z:\operatorname{Fin}8\to\mathbb C$ with $z_i=f_i$ for every original index, all 8 actual row equations, zero start and both coordinates nondecreasing. Its last vertex has positive imaginary part and squared real part greater than $26/5$. The last vertex has $\beta/z_7=\alpha_8z_7^2-b_8+E_8(z_7)/z_7$, $A\le9/1000$, $B\le0$, $C\le73/4000$, and wedge $(\Re z_7)^2-3(\Im z_7)^2\ge26/5$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthPrefixEight.lean, lines 8-87, SHA-256 298cbada5a001dda8c83a4098620f5bbb2522b189ffc52ce12f2c3829634a102.

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

theorem DerivativeChainContinuation.normalized_sixth_extend_prefix_seven (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) (f : Fin 7 → ℂ)
    (hfroot : ∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f i)=0)
    (hf0 : f 0=0) (hfr : Monotone (fun i => (f i).re)) (hfi : Monotone (fun i => (f i).im))
    (hfim : 0<(f 6).im) (hfX : 4<(f 6).re^2)
    (hfinv : β/f 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(f 6)^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (f 6)/f 6) :
    ∃ z : Fin 8 → ℂ,
      (∀ i : Fin 7,z i.castSucc=f i) ∧
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 7).im ∧ 26/5<(z 7).re^2 ∧
      β/z 7=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*(z 7)^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder (z 7)/z 7 ∧
      (sixthOcticRemainder (z 7)).re/(z 7).re≤9/1000 ∧
      (sixthOcticRemainder (z 7)).im/(z 7).im≤0 ∧
      (3*((sixthOcticRemainder (z 7)).re/(z 7).re)-(sixthOcticRemainder (z 7)).im/(z 7).im)/2≤73/4000 ∧
      26/5≤(z 7).re^2-3*(z 7).im^2 := by sorry
