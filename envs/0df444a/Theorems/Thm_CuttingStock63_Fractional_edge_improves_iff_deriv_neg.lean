-- Prove2me | Theorems.Thm_CuttingStock63_Fractional_edge_improves_iff_deriv_neg
-- name    : CuttingStock63.Fractional.edge_improves_iff_deriv_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:11.090925+00:00
-- url     : https://prove2.me/theorems/0fa6d5f7-700e-4dc9-b8e5-293fb09bd0d3
-- title:
--   Customer Tolerances, p. 883 — if dζ/dx_j is negative, increasing x_j decreases the objective, otherwise not
-- statement:
--   Let $c,d,x,v\in\mathbb R^n$, let $T>0$, and suppose the denominator $\sum_i d_i(x_i+\tau v_i)$ does not vanish for $\tau\in[0,T]$. Write $f(\tau)=\zeta(x+\tau v)$ for the ratio objective along the segment. Then:
--
--   1. if $f'(0)<0$, then $f(\tau)<f(0)$ for every $\tau\in(0,T]$: moving along $v$ strictly decreases the objective;
--   2. if $f'(0)\ge0$, then $f(0)\le f(\tau)$ for every $\tau\in[0,T]$: moving along $v$ does not decrease the objective anywhere on the segment.
--
--   With $v$ the edge of a nonbasic variable $x_j$, this is the paper's rule that a negative $d\zeta/dx_j$ means increasing $x_j$ decreases the objective, "otherwise not". It is the edge-level form of the optimality test.
--
--   **Formalization Note** The derivative is Mathlib's `deriv` of $\tau\mapsto\zeta(x+\tau v)$ at $0$, which is the true derivative because the denominator is nonzero at $\tau=0$. The page's claim is about the whole move along the edge, and "otherwise not" is read as: no point of the segment improves on $f(0)$.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 883, Customer Tolerances, sentence after eq. (5): "If this expression is negative, increasing x_j will decrease the objective function, otherwise not"

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem edge_improves_iff_deriv_neg {n : ℕ} (c d x v : Fin n → ℝ) (T : ℝ) (hT : 0 < T)
    (hden : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0 < 0 →
      ∀ τ ∈ Set.Ioc (0 : ℝ) T, fracObj c d (x + τ • v) < fracObj c d x) ∧
    (0 ≤ deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0 →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, fracObj c d x ≤ fracObj c d (x + τ • v)) := by sorry
end CuttingStock63.Fractional
