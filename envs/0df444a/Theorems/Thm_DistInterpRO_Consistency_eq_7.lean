-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_eq_7
-- name    : DistInterpRO.Consistency.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:49:37.1813+00:00
-- url     : https://prove2.me/theorems/5152900e-22aa-4342-8fe8-e09ab21b3fcf
-- title:
--   Eq. (7) — the box-robust objective is within $M_n + d(2\epsilon)$ of the true expected utility, with $M_n = C\|h_n - h^*\|_1$
-- statement:
--   Let $f:V\times\mathbb R^m\to\mathbb R$ have $f(v,\cdot)$ Borel measurable for every $v$ and $|f(v,x)|\le C$ for all $v,x$, and let $d$ be its equicontinuity modulus. Let $h^*$ be a probability density on $\mathbb R^m$ (nonnegative, Lebesgue integrable, $\int h^*=1$). Let $n\ge1$, $\epsilon>0$ and $x_1,\dots,x_n\in\mathbb R^m$; let $\mathcal Z_i$ be the boxes of radius $\epsilon$ around the $x_i$, $h_n$ the box kernel density estimator with bandwidth $\epsilon$, and
--   $$M_n=C\int_{\mathbb R^m}|h_n(x)-h^*(x)|\,dx.$$
--   Then for every $v\in V$,
--   $$\sum_{i=1}^n\frac1n\inf_{x_i'\in\mathcal Z_i}f(v,x_i')-M_n\ \le\ \int_{\mathbb R^m}f(v,x)h^*(x)\,dx\ \le\ \sum_{i=1}^n\frac1n\inf_{x_i'\in\mathcal Z_i}f(v,x_i')+M_n+d(2\epsilon).$$
--
--   This is Eq. (7) of the paper: the robust objective approximates the true expected utility uniformly in $v$, up to the $L^1$ error of the kernel density estimator and the modulus of continuity at twice the box radius.
--
--   **Formalization Note** The paper introduces $M_n$ only as "there exists $\{M_n\}\to0$ with probability 1" such that $\int f h_n\le\int f h^*+M_n$ for all $v$. Here $M_n$ is the explicit choice $C\|h_n-h^*\|_1$, which satisfies that inequality (and its symmetric counterpart) because $|f|\le C$, and which tends to $0$ almost surely by the $L^1$ consistency of the estimator. With this choice Eq. (7) is a deterministic statement, valid for every sample and every $v$. The integrals are Bochner integrals of integrable functions ($f(v,\cdot)$ bounded measurable, $h^*$ and $h_n$ integrable).
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 99, proof of Theorem 3.1, Eq. (7)

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem eq_7 {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (hstar_one : ∫ x, hstar x = 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) (v : V) :
    roObjective f ε xs v - C * (∫ x, |kde ε xs x - hstar x|) ≤ (∫ x, f v x * hstar x) ∧
      (∫ x, f v x * hstar x) ≤
        roObjective f ε xs v + C * (∫ x, |kde ε xs x - hstar x|) +
          modulus f (2 * ε) := by sorry

end DistInterpRO.Consistency
