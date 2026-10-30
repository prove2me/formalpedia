-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_validated_inverse
-- name    : DerivativeChainContinuation.sixth9_validated_inverse
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:47:39.529394+00:00
-- url     : https://prove2.me/theorems/b5c8fe80-daf2-408f-a68c-2ada65286e6c
-- title:
--   A validated analytic solution of the ninth-row inverse equation
-- statement:
--   For the exact polynomial data $P(t)$ and $G(t,w)$, there is $W:\mathbb C\to\mathbb C$ such that for $|t|\le2$,
--
--   $$|W(t)-P(t)|\le10^{-8},\qquad G(t,W(t))=0.$$
--
--   The function is holomorphic on $|t|<2$ and is real on the real interval $[-2,2]$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9ValidatedInverse.lean#L39-L75

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.sixth9_validated_inverse :
    ∃ W : ℂ → ℂ,
      (∀ t : ℂ,‖t‖ ≤ 2 → ‖W t-sixth9P t‖ ≤ 1/100000000 ∧ sixth9G t (W t)=0) ∧
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      ∀ x : ℝ,|x| ≤ 2 → (W (x:ℂ)).im=0 := by sorry
