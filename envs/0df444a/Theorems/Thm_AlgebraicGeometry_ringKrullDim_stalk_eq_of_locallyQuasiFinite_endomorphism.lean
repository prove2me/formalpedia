-- Prove2me | Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
-- name    : AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9a0756d6-b2cd-5af0-ae05-f6456485aeb5
-- title:
--   Locally quasi-finite endomorphisms preserve local dimension
-- statement:
--   Let $k$ be a field and let $X$ be a scheme equipped with a morphism $f \colon X \to \operatorname{Spec} k$ that is locally of finite type, with $X$ integral (its underlying space irreducible and its structure sheaf reduced). Let $h \colon X \to X$ be a morphism of schemes which is a morphism over $k$, in the sense that $h$ followed by $f$ equals $f$, and which is locally quasi-finite. Then for every point $x$ of $X$ the Krull dimension of the local ring of $X$ at $x$ equals the Krull dimension of the local ring of $X$ at the image point $h(x)$ under the map of underlying topological spaces:
--   $$\dim \mathcal{O}_{X,x} \;=\; \dim \mathcal{O}_{X,h(x)},$$
--   the dimensions being compared as elements of $\mathbb{N}_\infty$ extended by $-\infty$. No hypothesis of separatedness, quasi-compactness or surjectivity on $h$ is required, and $X$ need not be of finite type over $k$ globally.
--
--   This is the scheme-theoretic form of the dimension formula for integral schemes locally of finite type over a field, $\dim \mathcal{O}_{X,x} = \dim X - \operatorname{trdeg}_k \kappa(x)$, combined with the fact that a locally quasi-finite morphism induces finite residue field extensions, so that $\kappa(x)$ and $\kappa(h(x))$ have the same transcendence degree over $k$. It supplies the equality-of-dimensions input to the quasi-finite miracle-flatness argument used in [`AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism`](thm.html#AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism) and, through it, to the flatness of multiplication-by-$n$ on the relative group law of a Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [LocallyQuasiFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) := by sorry
