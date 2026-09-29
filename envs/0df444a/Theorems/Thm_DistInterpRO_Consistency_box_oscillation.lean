-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_box_oscillation
-- name    : DistInterpRO.Consistency.box_oscillation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:49:06.29816+00:00
-- url     : https://prove2.me/theorems/e2f3956f-2fc8-4e97-8c4d-6f5f3d2118eb
-- title:
--   Proof of Theorem 3.1 — the oscillation of $f(v,\cdot)$ over a box of radius $\epsilon$ is at most $d(2\epsilon)$
-- statement:
--   Let $f:V\times\mathbb R^m\to\mathbb R$ satisfy $|f(v,x)|\le C$ for all $v,x$, and let
--   $d(\epsilon)=\sup_{v,x,\|\delta\|_\infty\le\epsilon}|f(v,x)-f(v,x+\delta)|$. For every $v\in V$, every $x_i\in\mathbb R^m$ and every $\epsilon>0$, with $\mathcal Z_i=\{x_i+\delta\mid\|\delta\|_\infty\le\epsilon\}$,
--   $$\sup_{x\in\mathcal Z_i}f(v,x)-\inf_{x\in\mathcal Z_i}f(v,x)\ \le\ d(2\epsilon).$$
--
--   Together with the equicontinuity assumption $d(\epsilon)\to0$, this is what makes the box-robust objective close to the upper estimate by suprema in the proof of Theorem 3.1.
--
--   **Formalization Note** The supremum and infimum are real `⨆`/`⨅` over the nonempty box, bounded by $C$ in absolute value, so they are the true supremum and infimum; $d$ is a real supremum of quantities bounded by $2C$ over a nonempty index set.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 99, proof of Theorem 3.1, the display after 'Furthermore, note that'

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem box_oscillation {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) (v : V) (xi : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (⨆ x : box xi ε, f v x) - (⨅ x : box xi ε, f v x) ≤ modulus f (2 * ε) := by sorry

end DistInterpRO.Consistency
