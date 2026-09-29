-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/16fe94fb-cd39-532e-a8e5-18f0f3b50b96
-- title:
--   Relative dimension of a smooth irreducible K-scheme from one rational point
-- statement:
--   Let $K$ be a field and let $f \colon X \to \operatorname{Spec} K$ be a morphism of schemes (all in a single universe) which is smooth, with $X$ an irreducible topological space. Let $z \colon \operatorname{Spec} K \to X$ be a section of $f$, i.e. $z$ followed by $f$ is the identity of $\operatorname{Spec} K$, so that $z$ is a $K$-rational point of $X$; write $x = z(\mathfrak{m}_K)$ for the image under $z$ of the closed point of $\operatorname{Spec} K$. Let $n$ be a natural number and assume that the Zariski cotangent space $\mathfrak{m}_x/\mathfrak{m}_x^2$ of the local ring $\mathcal{O}_{X,x}$ (the stalk of the structure presheaf of $X$ at $x$) has finite-dimensional rank exactly $n$ over the residue field of $\mathcal{O}_{X,x}$. The conclusion is that $f$ is smooth of relative dimension $n$, in the sense of Mathlib's `SmoothOfRelativeDimension n f`.
--
--   This is the standard fact that the relative dimension of a smooth irreducible scheme over a field may be read off from the Zariski tangent space at a single rational point — the form in which the dimension of a group variety is computed from its Lie algebra. It is used in the project to compute the relative dimension of curve models and of the smooth schemes attached to fake elliptic curves in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [IrreducibleSpace X]
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n) :
    SmoothOfRelativeDimension n f := by sorry
