-- Prove2me | Theorems.Thm_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
-- name    : AlgebraicGeometry.finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d406a8eb-046a-5d8d-a7d1-e94d6af951e3
-- title:
--   Cotangent space at a rational point has dimension n
-- statement:
--   Let $K$ be a field and let $X$ be a scheme, both in a fixed universe, and let $f : X \to \operatorname{Spec} K$ be a morphism of schemes which is smooth of relative dimension $n$ for a natural number $n$, in the sense of Mathlib's typeclass `SmoothOfRelativeDimension n f`. Let $z : \operatorname{Spec} K \to X$ be a morphism which is a section of $f$, that is, $z$ followed by $f$ equals the identity of $\operatorname{Spec} K$; thus $z$ is a $K$-rational point of $X$. Write $x = z(\mathfrak{p})$ for the image under the underlying continuous map of $z$ of the closed point of $\operatorname{Spec} K$, and let $\mathcal{O}_{X,x}$ be the stalk of the structure presheaf of $X$ at $x$, a local ring. The assertion is that the Zariski cotangent space of $\mathcal{O}_{X,x}$, namely $\mathfrak{m}_x/\mathfrak{m}_x^2$ regarded as a module over the residue field of $\mathcal{O}_{X,x}$, has finite rank exactly $n$ over that residue field.
--
--   This is the standard characterisation of smoothness of relative dimension $n$ at a rational point: the Zariski cotangent space there has dimension equal to the relative dimension. It is used to produce local coordinates on smooth charts around a rational point and, in the study of elliptic curves with good reduction, to compute the dimension of the cotangent space of the kernel of the counit of a relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
    Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n := by sorry
