-- Prove2me | Theorems.Thm_DerivativeChainPrivate_bounded_holomorphic_contraction
-- name    : DerivativeChainPrivate.bounded_holomorphic_contraction
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:43:07.578009+00:00
-- url     : https://prove2.me/theorems/c6c213c9-aa13-498d-bb71-07e1cdb7e1e2
-- title:
--   A bounded holomorphic fixed-point family
-- statement:
--   Let $F:\mathbb C^2\to\mathbb C$ be jointly holomorphic everywhere, $R>0$, and $M\ge0$. For $|t|\le R$, assume $F(t,\cdot)$ maps $|v|\le M$ into itself and satisfies $|F(t,v)-F(t,w)|\le|v-w|/2$ there. Assume also that $F(x,y)$ is real for every real $x,y$. There is $Y:\mathbb C\to\mathbb C$ with $|Y(t)|\le M$ and $F(t,Y(t))=Y(t)$ for $|t|\le R$, holomorphic on $|t|<R$, and real on the real interval $[-R,R]$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/HolomorphicContraction.lean#L9-L92

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped NNReal

theorem DerivativeChainPrivate.bounded_holomorphic_contraction (F : ℂ → ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hhol : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2))
    (hmap : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v : ℂ, ‖v‖ ≤ M → ‖F t v‖ ≤ M)
    (hcontract : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v w : ℂ, ‖v‖ ≤ M → ‖w‖ ≤ M →
      ‖F t v-F t w‖ ≤ (1/2)*‖v-w‖)
    (hreal : ∀ x y : ℝ, (F (x:ℂ) (y:ℂ)).im=0) :
    ∃ Y : ℂ → ℂ,
      (∀ t : ℂ, ‖t‖ ≤ R → ‖Y t‖ ≤ M ∧ F t (Y t)=Y t) ∧
      DifferentiableOn ℂ Y (Metric.ball 0 R) ∧
      ∀ x : ℝ, |x| ≤ R → (Y (x:ℂ)).im=0 := by sorry
