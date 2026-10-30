-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_eight
-- name    : DerivativeChainContinuation.normalized_sixth_prefix_eight
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:21:15.959962+00:00
-- url     : https://prove2.me/theorems/2bbf6fee-6646-45dc-8fd8-4e6d7bd62680
-- title:
--   An actual coordinate-monotone prefix through all 8 rows
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. For every $\Re\beta\ge0$, $\Im\beta>0$, there is $z:\operatorname{Fin}8\to\mathbb C$ with $(D^{17-i}F_\beta)(z_i)=0$ for every index, $z_0=0$, and both coordinates nondecreasing. The last vertex has positive imaginary part and squared real part greater than $26/5$. Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. The last vertex satisfies the selected eighth-row inverse, $A\le9/1000$, $B\le0$, $C\le73/4000$, and wedge at least $26/5$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthPrefixEight.lean, lines 89-103, SHA-256 298cbada5a001dda8c83a4098620f5bbb2522b189ffc52ce12f2c3829634a102.

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

theorem DerivativeChainContinuation.normalized_sixth_prefix_eight (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) :
    ∃ z : Fin 8 → ℂ,
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 7).im ∧ 26/5<(z 7).re^2 ∧
      β/z 7=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*(z 7)^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder (z 7)/z 7 ∧
      (sixthOcticRemainder (z 7)).re/(z 7).re≤9/1000 ∧
      (sixthOcticRemainder (z 7)).im/(z 7).im≤0 ∧
      (3*((sixthOcticRemainder (z 7)).re/(z 7).re)-(sixthOcticRemainder (z 7)).im/(z 7).im)/2≤73/4000 ∧
      26/5≤(z 7).re^2-3*(z 7).im^2 := by sorry
