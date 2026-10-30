-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_seven
-- name    : DerivativeChainContinuation.normalized_sixth_prefix_seven
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:17:04.700564+00:00
-- url     : https://prove2.me/theorems/e0250d95-1e0c-4daf-9547-9bb2492e3cb2
-- title:
--   An actual coordinate-monotone prefix through all 7 rows
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. For every $\Re\beta\ge0$, $\Im\beta>0$, there is $z:\operatorname{Fin}7\to\mathbb C$ with $(D^{17-i}F_\beta)(z_i)=0$ for every index, $z_0=0$, and both coordinates nondecreasing. The last vertex has positive imaginary part and squared real part greater than $4$. Write $S_7(\beta,z)=(1360/13)\beta^2z-35\beta z^4+85\beta z^2-(1445/78)\beta+z^7-7z^5+(595/48)z^3-(1445/312)z$, $\alpha_7=(455-3\sqrt{15145})/2720$, $b_7=13/32-77\sqrt{15145}/37280$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. The last vertex satisfies the selected seventh-row inverse, $A\le39/2000$, $B\le0$, $C\le39/1000$, and wedge at least $4$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthPrefixSeven.lean, lines 90-107, SHA-256 381348cfe7fbbc0f8023a25a05e09ec43924c3d627707ace1ec6ee2de6541edb.

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

theorem DerivativeChainContinuation.normalized_sixth_prefix_seven (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) :
    ∃ z : Fin 7 → ℂ,
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 6).im ∧ 4<(z 6).re^2 ∧
      β/z 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(z 6)^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (z 6)/z 6 ∧
      (sixthSepticRemainder (z 6)).re/(z 6).re≤39/2000 ∧
      (sixthSepticRemainder (z 6)).im/(z 6).im≤0 ∧
      (3*((sixthSepticRemainder (z 6)).re/(z 6).re)-(sixthSepticRemainder (z 6)).im/(z 6).im)/2≤39/1000 ∧
      4≤(z 6).re^2-3*(z 6).im^2 := by sorry
