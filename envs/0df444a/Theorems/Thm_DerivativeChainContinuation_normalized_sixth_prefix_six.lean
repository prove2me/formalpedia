-- Prove2me | Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_six
-- name    : DerivativeChainContinuation.normalized_sixth_prefix_six
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:17:00.827552+00:00
-- url     : https://prove2.me/theorems/dd70c6db-eb3e-4fd7-9e31-00b2326b1b4b
-- title:
--   An actual coordinate-monotone prefix through all 6 rows
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. For every $\Re\beta\ge0$, $\Im\beta>0$, there is $z:\operatorname{Fin}6\to\mathbb C$ with $(D^{17-i}F_\beta)(z_i)=0$ for every index, $z_0=0$, and both coordinates nondecreasing. The last vertex has positive imaginary part and squared real part greater than $7/2$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthPrefixSix.lean, lines 80-88, SHA-256 474ec7a0a1b1f04dfcf804e5046432fe80812a3375b2f368a821d356334f9399.

import Mathlib
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

theorem DerivativeChainContinuation.normalized_sixth_prefix_six (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) :
    ∃ z : Fin 6 → ℂ,
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 5).im ∧ 7/2<(z 5).re^2 := by sorry
