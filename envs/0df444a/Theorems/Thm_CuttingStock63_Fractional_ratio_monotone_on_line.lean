-- Prove2me | Theorems.Thm_CuttingStock63_Fractional_ratio_monotone_on_line
-- name    : CuttingStock63.Fractional.ratio_monotone_on_line
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:55:06.501425+00:00
-- url     : https://prove2.me/theorems/53950aef-fe20-4629-b348-3013fd867b48
-- title:
--   Customer Tolerances, p. 882 — a ratio of linear functions is uniformly increasing or decreasing along a line avoiding the zeros of its denominator
-- statement:
--   Let $c,d,x,v\in\mathbb R^n$ and consider the ratio of two linear functions restricted to the line through $x$ in direction $v$,
--   $$f(\tau)=\zeta(x+\tau v)=\frac{\sum_i c_i(x_i+\tau v_i)}{\sum_i d_i(x_i+\tau v_i)},\qquad D(\tau)=\sum_i d_i(x_i+\tau v_i).$$
--   Let $I\subseteq\mathbb R$ be an interval on which the denominator $D$ does not vanish. Then:
--
--   1. $f$ is strictly increasing on $I$, or strictly decreasing on $I$, or constant on $I$;
--   2. the derivative changes along $I$ only by a positive factor: for all $\tau,\tau'\in I$,
--   $$f'(\tau)\,D(\tau)^2=f'(\tau')\,D(\tau')^2 .$$
--   In particular $f'$ has the same sign at every point of $I$.
--
--   This is what lets the simplex method be used for a ratio objective: along an edge the objective cannot first improve and then deteriorate, so the local test at a vertex decides the whole edge.
--
--   **Formalization Note** The page says the derivative "will have the same value $v$" at every point of the line; this is false when the denominator is not constant along the line (the derivative of $(\alpha+\beta\tau)/(\gamma+\delta\tau)$ is $(\beta\gamma-\alpha\delta)/(\gamma+\delta\tau)^2$). The statement formalizes the correct version, which is what "uniformly increasing or decreasing" and the simplex argument need: the derivative times the squared denominator is constant. The page's "rational function" is the ratio $z_1/z_2$ of two linear functions of p. 881, Derman's published `fracObj`. The page speaks of a whole line; the statement is for any interval $I$ (the whole line being $I=\mathbb R$), which is the stronger form used along a segment of the feasible set.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 882, Customer Tolerances, paragraph "It is easy to show by direct differentiation …"

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem ratio_monotone_on_line {n : ℕ} (c d x v : Fin n → ℝ) (I : Set ℝ)
    (hI : IsPreconnected I) (hden : ∀ τ ∈ I, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (StrictMonoOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      StrictAntiOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      ∀ τ ∈ I, ∀ τ' ∈ I, fracObj c d (x + τ • v) = fracObj c d (x + τ' • v)) ∧
    ∀ τ ∈ I, ∀ τ' ∈ I,
      deriv (fun s : ℝ => fracObj c d (x + s • v)) τ * (∑ i, d i * (x + τ • v) i) ^ 2 =
        deriv (fun s : ℝ => fracObj c d (x + s • v)) τ' * (∑ i, d i * (x + τ' • v) i) ^ 2 := by sorry
end CuttingStock63.Fractional
