-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_polynomial_contraction
-- name    : DerivativeChainContinuation.finite_polynomial_contraction
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:45:17.038448+00:00
-- url     : https://prove2.me/theorems/3e8b6e49-3e02-49ca-971a-25d6fd1b2f95
-- title:
--   A finite coefficient criterion for a holomorphic fixed-point family
-- statement:
--   Let $d\ge0$, entire functions $c_j:\mathbb C\to\mathbb C$ and bounds $B_j\ge0$ be indexed by $0\le j\le d$. Let $R>0$, $M\ge0$, assume $|c_j(t)|\le B_j$ for $|t|\le R$, and suppose every $c_j$ is real on the real axis. If
--
--   $$\sum_{j=0}^{d}B_jM^j\le M,\qquad\sum_{j=1}^{d}jB_jM^{j-1}\le1/2,$$
--
--   there is $Y$ with $|Y(t)|\le M$ and $Y(t)=\sum_jc_j(t)Y(t)^j$ on $|t|\le R$, holomorphic on $|t|<R$, and real for real $|t|\le R$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FinitePolynomialContraction.lean#L28-L73

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FinitePolynomialContraction
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.finite_polynomial_contraction (d : ℕ) (c : Fin (d+1) → ℂ → ℂ)
    (B : Fin (d+1) → ℝ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hB : ∀ j,0 ≤ B j) (hc : ∀ j,Differentiable ℂ (c j))
    (hbound : ∀ t : ℂ,‖t‖ ≤ R → ∀ j,‖c j t‖ ≤ B j)
    (hmap : (∑ j,B j*M^j.val) ≤ M)
    (hcontract : (∑ j,B j*(j.val:ℝ)*M^(j.val-1)) ≤ 1/2)
    (hreal : ∀ j,∀ x : ℝ,(c j (x:ℂ)).im=0) :
    ∃ Y : ℂ → ℂ,
      (∀ t : ℂ,‖t‖ ≤ R → ‖Y t‖ ≤ M ∧ polynomialContractionMap d c t (Y t)=Y t) ∧
      DifferentiableOn ℂ Y (Metric.ball 0 R) ∧
      ∀ x : ℝ,|x| ≤ R → (Y (x:ℂ)).im=0 := by sorry
