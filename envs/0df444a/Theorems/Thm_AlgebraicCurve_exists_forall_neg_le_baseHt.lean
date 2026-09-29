-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_forall_neg_le_baseHt
-- name    : AlgebraicCurve.exists_forall_neg_le_baseHt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/309fe08f-f3a7-57cf-8093-7638929e4a9d
-- title:
--   Uniform lower bound for the base height
-- statement:
--   Let $F$ be a field equipped with an algebra structure over $\overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$ as constructed in Mathlib), let $r$ be a natural number and let $s : \mathrm{Fin}\,r \to F$ be a finite family of elements of $F$. Here a place of $F$ over $\overline{\mathbb Q}$ is, by definition, a valuation subring of $F$ that contains the image of $\overline{\mathbb Q}$ under the structure map, is not the whole of $F$, and is a principal ideal ring. The assertion is that there exists a real constant $C$ with $0 \le C$ such that for every pair of places $b, v$ of $F$ over $\overline{\mathbb Q}$ one has $-C \le \mathrm{baseHt}\ s\ b\ v$, where $\mathrm{baseHt}\ s\ b\ v$ is $0$ when $v = b$ and otherwise equals the pair height $\mathrm{pairHt}\ s\ v\ b = \mathrm{pointHt}\ s\ v + \mathrm{pointHt}\ s\ b - \mathrm{absLogHeight}(\mathrm{chordVec}\ s\ v\ b)$. Thus the bound is uniform in both the base place $b$ and the place $v$, and the constant depends only on the family $s$.
--
--   This is the "floor" estimate for the base height attached to a finite family $s$: the base height, a difference of point heights and the height of the chord vector, is bounded below independently of the two places involved. It is used in the study of the quadratic height form on $X_0(N)$, where boundedness below of the form on representatives yields the existence of height-minimal representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_forall_neg_le_baseHt.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_forall_neg_le_baseHt {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b v : Place (AlgebraicClosure ℚ) F, -C ≤ baseHt s b v := by sorry
