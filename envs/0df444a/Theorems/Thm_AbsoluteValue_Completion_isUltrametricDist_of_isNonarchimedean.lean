-- Prove2me | Theorems.Thm_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean
-- name    : AbsoluteValue.Completion.isUltrametricDist_of_isNonarchimedean
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/56be8c66-65a1-5e6e-9575-58c034076889
-- title:
--   Completion at a non-archimedean absolute value is ultrametric
-- statement:
--   Let $K$ be a field and let $v \colon K \to \mathbb{R}$ be an absolute value on $K$ in the sense of Mathlib's `AbsoluteValue`, and suppose $v$ is non-archimedean, i.e. $v(x+y) \le \max(v(x), v(y))$ for all $x, y \in K$. The conclusion is that `v.Completion`, the uniform-space completion of $K$ equipped with the metric coming from $v$ (Mathlib's `WithAbs v`), which carries the structure of a complete normed field, satisfies `IsUltrametricDist`: the distance function on the completion obeys the strong triangle inequality $\operatorname{dist}(a,c) \le \max(\operatorname{dist}(a,b), \operatorname{dist}(b,c))$ for all $a, b, c$ in the completion, equivalently $\lVert a + b \rVert \le \max(\lVert a \rVert, \lVert b \rVert)$ for the norm induced by $v$. The statement is an instance-shaped fact: it produces the `IsUltrametricDist` typeclass datum for the completion from the non-archimedean hypothesis on $v$ itself.
--
--   This is the standard observation that the completion of a field at a non-archimedean absolute value is again non-archimedean, so that $\widehat{K}_v$ is a complete ultrametric normed field. It supplies the ultrametric structure used when evaluating power series over such a completion, and is invoked in the Jensen-type estimate [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AbsoluteValue.Completion.isUltrametricDist_of_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    IsUltrametricDist v.Completion := by sorry
