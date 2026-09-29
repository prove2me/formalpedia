-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
-- name    : AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/47e9412c-5960-5652-915f-84d5f41faefe
-- title:
--   Quasi-finiteness at a point descends along base change
-- statement:
--   Let $X$, $Y$, $X'$, $Y'$ be schemes (in a fixed universe) and let $f : X \to Y$, $f' : X' \to Y'$, $p : X' \to X$, $q : Y' \to Y$ be morphisms forming a cartesian square, in the sense that `IsPullback p f' f q` holds: the square with $p$ followed by $f$ equal to $f'$ followed by $q$ commutes and exhibits $X'$ as the fibre product of $X$ and $Y'$ over $Y$. Assume $f$ is locally of finite type and $f'$ is locally quasi-finite. Let $y'$ be a point of $Y'$ and $x$ a point of $X$ whose image satisfies $f(x) = q(y')$ as points of the underlying topological space of $Y$. Then $f$ is quasi-finite at $x$ in the sense of Mathlib's `Scheme.Hom.QuasiFiniteAt`. Thus the hypothesis on the base change is global (the whole morphism $f'$ is locally quasi-finite) while the conclusion is pointwise, at an arbitrary point of $X$ lying over a point in the image of $q$; no surjectivity of $q$ is assumed, and nothing is claimed at points of $X$ over $Y \setminus q(Y')$.
--
--   This is the descent direction of the statement that quasi-finiteness at a point is insensitive to base change, for morphisms locally of finite type; the ascent direction and the identification of fibres are already available in Mathlib. It is used in the construction of sections generating twists of a module away from a closed set under a hypothesis on geometric fibres ([`AlgebraicGeometry.Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x := by sorry
