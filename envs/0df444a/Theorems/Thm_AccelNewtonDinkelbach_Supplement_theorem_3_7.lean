-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_theorem_3_7
-- name    : AccelNewtonDinkelbach.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:02:37.457731+00:00
-- url     : https://prove2.me/theorems/d5567834-d068-4079-9b44-eea74fa23d3a
-- title:
--   Theorem 3.7 — a linear fractional program has value $-\infty$ exactly under one of two certificates
-- statement:
--   Let $D\subseteq\mathbb R^m$ be a polyhedron and let $c,d\in\mathbb R^m$, with at least one $x\in D$ satisfying $d^\top x>0$. Then
--
--   $$\inf_{x\in D,\ d^\top x>0}\frac{c^\top x}{d^\top x}=-\infty$$
--
--   if and only if either (1) some $x\in D$ has $c^\top x<0$ and $d^\top x=0$, or (2) some recession direction $r$ of all of $D$ has $c^\top r<0$ and $d^\top r=0$.
--
--   This is the paper's unboundedness characterization for linear fractional programming.
--
--   Differences from the source:
--   - encoding: vectors in R^m and an extended-real infimum → vectors indexed by Fin m and an EReal sInf; reason: the representation has the same feasible points and records unboundedness as −∞
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 3.7, pp.9–10

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_LinearFractionalProgram

namespace AccelNewtonDinkelbach.Supplement

open LinearFractionalProgram

set_option autoImplicit false

/-- **Theorem 3.7 (linear fractional programming unboundedness).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 3.7, pp.9–10.

For a polyhedron `D` with at least one point of positive denominator, `(F)` has value `−∞`
iff either a point of `D`, or a recession direction of all of `D`, has negative numerator and
zero denominator.  The value is extended-real, so unboundedness is literally equality to `⊥`. -/
theorem theorem_3_7 {m : ℕ} (P : LinearFractionalProgram m) (hpoly : P.IsPolyhedron)
    (hfeas : ∃ x, P.Feasible x) :
    P.value = ⊥ ↔
      (∃ x ∈ P.D, dot P.c x < 0 ∧ dot P.d x = 0) ∨
      (∃ r, dot P.c r < 0 ∧ dot P.d r = 0 ∧ P.IsRecessionDirection r) := by sorry

end AccelNewtonDinkelbach.Supplement
