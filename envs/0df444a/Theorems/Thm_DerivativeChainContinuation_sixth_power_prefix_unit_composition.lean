-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth_power_prefix_unit_composition
-- name    : DerivativeChainContinuation.sixth_power_prefix_unit_composition
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:33:15.628278+00:00
-- url     : https://prove2.me/theorems/b57d7bfd-0527-4d44-bf85-0304617a14f6
-- title:
--   The exact normalized cubic sixth-power composition
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Let $\rho=\sqrt{17/2}$, $\lambda=1/\rho$, and $\Gamma(\beta)=136\beta/\rho^3$. For every $\beta$, $F_\beta\circ(\rho X)=\rho^{18}(X^3-X-\Gamma(\beta))^6$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/SixthPhysicalNormalization.lean, lines 66-71, SHA-256 1dfc9eeb7a92d74ee64cdbdf176189ea94222551f0de4cfd6aee1274fcfeb4e8.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
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

theorem DerivativeChainContinuation.sixth_power_prefix_unit_composition (β : ℂ) :
    ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ).comp (C 0+C (sixthPrefixRadius:ℂ)*X)=
      C ((sixthPrefixRadius:ℂ)^18)*(X^3-X-C (sixthPhysicalParameter β))^6 := by sorry
