-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth_actual_rows_rescale
-- name    : DerivativeChainContinuation.sixth_actual_rows_rescale
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:35:44.807923+00:00
-- url     : https://prove2.me/theorems/bad595f3-bb23-4330-820a-ea209ef1dcea
-- title:
--   Physical normalization transports every actual derivative order
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Let $\rho=\sqrt{17/2}$, $\lambda=1/\rho$, and $\Gamma(\beta)=136\beta/\rho^3$. For every complex $\beta,z$ and natural $k$, $(D^kF_\beta)(\rho z)=0$ if and only if $D^k[(X^3-X-\Gamma(\beta))^6](z)=0$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/SixthPhysicalNormalization.lean, lines 73-87, SHA-256 1dfc9eeb7a92d74ee64cdbdf176189ea94222551f0de4cfd6aee1274fcfeb4e8.

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

theorem DerivativeChainContinuation.sixth_actual_rows_rescale (β z : ℂ) (k : ℕ) :
    (derivative^[k] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval ((sixthPrefixRadius:ℂ)*z)=0 ↔
      (derivative^[k] ((X^3-X-C (sixthPhysicalParameter β))^6 : Polynomial ℂ)).eval z=0 := by sorry
