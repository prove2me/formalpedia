-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_roObjective_le_integral_kde
-- name    : DistInterpRO.Consistency.roObjective_le_integral_kde
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:48:36.366664+00:00
-- url     : https://prove2.me/theorems/ca3d58bd-f242-457b-ac35-5a2915daab0c
-- title:
--   Proof of Theorem 3.1 — the box-robust objective is at most the expectation under $h_n$
-- statement:
--   Let $V$ be a set of decisions and $f:V\times\mathbb R^m\to\mathbb R$ a utility with $f(v,\cdot)$ Borel measurable for every $v$ and $|f(v,x)|\le C$ for all $v,x$. Let $n\ge1$, $\epsilon>0$, $x_1,\dots,x_n\in\mathbb R^m$, $\mathcal Z_i=\{x_i+\delta\mid\|\delta\|_\infty\le\epsilon\}$, and let $h_n$ be the box kernel density estimator with bandwidth $\epsilon$. Then for every $v\in V$,
--   $$\sum_{i=1}^n\frac1n\inf_{x_i'\in\mathcal Z_i}f(v,x_i')\ \le\ \int_{\mathbb R^m}f(v,x)\,h_n(x)\,dx.$$
--
--   In the paper this inequality follows from $h_n\in\mathcal P_n$ and the equivalence (6) of the robust objective with a worst-case expectation over $\mathcal P_n$. It is the lower half of the comparison between the robust objective and the true expected utility.
--
--   **Formalization Note** The left side is the box-robust objective $\frac1n\sum_i\inf_{\|\delta\|_\infty\le\epsilon}f(v,x_i+\delta)$; the infima are real infima over nonempty sets bounded below by $-C$. The integral is a Bochner integral against Lebesgue measure; the integrand is integrable because $f(v,\cdot)$ is bounded and measurable and $h_n$ is bounded with compact support.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 99, proof of Theorem 3.1, the display after 'which by Equation (6) implies'

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem roObjective_le_integral_kde {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) (v : V) :
    roObjective f ε xs v ≤ ∫ x, f v x * kde ε xs x := by sorry

end DistInterpRO.Consistency
