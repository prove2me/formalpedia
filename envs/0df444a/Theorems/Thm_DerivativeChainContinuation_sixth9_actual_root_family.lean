-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_actual_root_family
-- name    : DerivativeChainContinuation.sixth9_actual_root_family
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:41:56.700854+00:00
-- url     : https://prove2.me/theorems/a996bbe8-5f2b-4d30-9b41-ba92080ff96c
-- title:
--   Actual ninth-derivative roots along a validated parameter map
-- statement:
--   There is $W:\mathbb C\to\mathbb C$, holomorphic on $|t|<2$, real for real $|t|\le2$, with $|W(t)-P(t)|\le10^{-8}$ and $G(t,W(t))=0$ whenever $|t|\le2$. For every nonzero $z$ with $|z^{-1}|^2\le2$, define $\beta=z^3W((z^{-1})^2)$. Then
--
--   $$\left[(X^3-X-\beta)^6\right]^{(9)}(z)=0.$$
--
--   The parameter is defined from z by this formula; no complete eighteen-row list is asserted.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9RootFamily.lean#L8-L20

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

theorem DerivativeChainContinuation.sixth9_actual_root_family :
    ∃ W : ℂ → ℂ,
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      (∀ t : ℂ,‖t‖ ≤ 2 → ‖W t-sixth9P t‖ ≤ 1/100000000 ∧ sixth9G t (W t)=0) ∧
      (∀ x : ℝ,|x| ≤ 2 → (W (x:ℂ)).im=0) ∧
      ∀ z : ℂ,z ≠ 0 → ‖z⁻¹‖^2 ≤ 2 →
        (derivative^[9] ((X^3-X-C (z^3*W ((z⁻¹)^2)))^6)).eval z=0 := by sorry
