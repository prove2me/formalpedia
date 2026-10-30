-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_prefix_actual_root_family
-- name    : DerivativeChainContinuation.sixth9_prefix_actual_root_family
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:02:31.253974+00:00
-- url     : https://prove2.me/theorems/11bf095b-466c-4ea6-8a4b-e5cf3619a0bf
-- title:
--   A holomorphic ninth-row root-locus family
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Let $\rho=\sqrt{17/2}$, $\lambda=1/\rho$, and $\Gamma(\beta)=136\beta/\rho^3$. There exists $W:\mathbb C\to\mathbb C$, holomorphic on $|t|<2$, with $|W(t)-P_9(t)|\le10^{-8}$ and $G_9(t,W(t))=0$ whenever $|t|\le2$, and real on $[-2,2]$. For every nonzero $z$ with $|z^{-1}|^2\le2$, define $\beta=(\rho^3/136)z^3W(z^{-2})$. Then $(D^9F_\beta)(\rho z)=0$. The functions $P_9,G_9$ are the exact canonical sixth9 certificates. This parametrizes roots; it does not construct a ninth-row extension at every prescribed parameter.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/SixthPhysicalNormalization.lean, lines 100-120, SHA-256 1dfc9eeb7a92d74ee64cdbdf176189ea94222551f0de4cfd6aee1274fcfeb4e8.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
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

theorem DerivativeChainContinuation.sixth9_prefix_actual_root_family :
    ∃ W : ℂ → ℂ,
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      (∀ t : ℂ,‖t‖≤2 → ‖W t-sixth9P t‖≤1/100000000 ∧ sixth9G t (W t)=0) ∧
      (∀ x : ℝ,|x|≤2 → (W (x:ℂ)).im=0) ∧
      ∀ z : ℂ,z≠0 → ‖z⁻¹‖^2≤2 →
        let β:=((sixthPrefixRadius:ℂ)^3/136)*(z^3*W ((z⁻¹)^2))
        (derivative^[9] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval
          ((sixthPrefixRadius:ℂ)*z)=0 := by sorry
