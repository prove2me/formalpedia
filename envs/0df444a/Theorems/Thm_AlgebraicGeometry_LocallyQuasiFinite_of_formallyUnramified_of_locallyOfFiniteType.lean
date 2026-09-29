-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/18d13bd5-9114-5cc7-92a2-c935c293dee9
-- title:
--   Formally unramified plus locally of finite type gives locally quasi-finite
-- statement:
--   Let $X$ and $Y$ be schemes and let $f \colon X \to Y$ be a morphism of schemes. Assume that $f$ is formally unramified, in the sense of Mathlib's `AlgebraicGeometry.FormallyUnramified`, and that $f$ is locally of finite type, in the sense of `AlgebraicGeometry.LocallyOfFiniteType`. The conclusion is that $f$ is locally quasi-finite, i.e. `AlgebraicGeometry.LocallyQuasiFinite f` holds; equivalently, by the affine-local characterisation used in the proof, for every affine open $U \subseteq Y$ and every affine open $V \subseteq X$ with $V$ mapped into $U$ by $f$, the induced ring homomorphism $\Gamma(Y, U) \to \Gamma(X, V)$ on sections is quasi-finite as an algebra map. All three notions are Mathlib's morphism properties for schemes; no hypothesis of separatedness, flatness or quasi-compactness is imposed, and no finiteness assumption is made on the base.
--
--   This is the classical implication "unramified morphisms locally of finite type are locally quasi-finite" (EGA IV, 17.4.1), in its scheme-theoretic form. It is used in the project to obtain quasi-finiteness of maps verified to be formally unramified by an infinitesimal lifting criterion, notably for multiplication by $n$ on an abelian scheme with $n$ invertible, and is cited by [`AlgebraicGeometry.finite_torsion_of_isProper_of_smooth`](thm.html#AlgebraicGeometry.finite_torsion_of_isProper_of_smooth) and by [`GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit`](thm.html#GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.FormallyUnramified f] [AlgebraicGeometry.LocallyOfFiniteType f] :
    AlgebraicGeometry.LocallyQuasiFinite f := by sorry
