-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_eq_5_5_5_6
-- name    : CvitanicKaratzas92.Optimality.eq_5_5_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:12:31.595028+00:00
-- url     : https://prove2.me/theorems/c6c4b89e-8c32-446f-be60-f52666abe04d
-- title:
--   (5.5)–(5.6) — $U(I(y))\ge U(x)+y[I(y)-x]$ and $\tilde U(U'(x))+x[U'(x)-y]\le\tilde U(y)$
-- statement:
--   Let $U$ be a utility function (strictly increasing, strictly concave, $C^1$ on $(0,\infty)$, with $U'(0+)=\infty$, $U'(\infty)=0$), let $I$ be the inverse of $U'$ and $\tilde U(y)=\max_{x>0}[U(x)-xy]$ its Legendre–Fenchel transform. Then for all $x>0$ and $y>0$,
--   $$U(I(y))\ge U(x)+y\,[\,I(y)-x\,],\qquad \tilde U(U'(x))+x\,[\,U'(x)-y\,]\le\tilde U(y).$$
--
--   These inequalities are used in the proof of Lemma 7.2 and in the implication (E) $\Rightarrow$ (D) of Theorem 10.1.
--
--   **Formalization Note** $I(y)=\inf\{x>0:\ U'(x)\le y\}$ and $\tilde U(y)=\sup\{U(x)-xy:\ x>0\}$, as in the definition file.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 772, Section 5, (5.5)–(5.6)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Utility

open Set
open scoped Topology

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), (5.5)–(5.6), p. 772: for a utility function `U` with inverse
marginal `I` and Legendre–Fenchel transform `Ũ`, and all `x > 0`, `y > 0`,
`U(I(y)) ≥ U(x) + y[I(y) − x]` and `Ũ(U'(x)) + x[U'(x) − y] ≤ Ũ(y)`. -/
theorem eq_5_5_5_6 (U : ℝ → ℝ) (hU : IsUtility U) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    U x + y * (invMarginal U y - x) ≤ U (invMarginal U y) ∧
      conj U (deriv U x) + x * (deriv U x - y) ≤ conj U y := by sorry


end CvitanicKaratzas92.Optimality
