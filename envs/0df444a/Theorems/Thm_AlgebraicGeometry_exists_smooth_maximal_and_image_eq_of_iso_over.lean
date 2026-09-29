-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over
-- name    : AlgebraicGeometry.exists_smooth_maximal_and_image_eq_of_iso_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/191579dd-c8e1-55bb-9c31-430ae83e25f4
-- title:
--   Maximal smooth open of a morphism, stable under automorphisms over S
-- statement:
--   Let $f \colon X \to S$ be a morphism of schemes and let $n$ be a natural number. Assume that for every open subscheme $V$ of $X$ (an element of `X.Opens`), if the composite of the inclusion $V.\iota$ with $f$ is smooth, then it is smooth of relative dimension $n$. The conclusion asserts the existence of an open $U \subseteq X$ with four properties: (i) the composite $U.\iota$ followed by $f$ is smooth of relative dimension $n$; (ii) every open $V$ such that $V \to S$ is smooth satisfies $V \le U$, so $U$ is the largest such open; (iii) for every isomorphism $w \colon X \cong X$ with $w.\mathrm{hom}$ followed by $f$ equal to $f$, the scheme-theoretic open image $w.\mathrm{hom}\,''^{\mathcal U}\,U$ equals $U$; and (iv) for every such $w$, every scheme $T$ and every morphism $\varepsilon \colon T \to X$ whose underlying topological range is contained in $U$, the range of the underlying map of $\varepsilon$ followed by $w.\mathrm{hom}$ is again contained in $U$.
--
--   This is the existence of the maximal open locus on which a morphism of schemes is smooth, together with its invariance under automorphisms of $X$ over $S$; the relative-dimension clause is imposed as a hypothesis rather than derived. It supplies the smooth-locus data, its maximality, and the fact that a section landing in the smooth locus still does so after composing with an automorphism over the base, as used in [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart) for models of modular curves with the Atkin–Lehner automorphism and the cusp at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u in

theorem AlgebraicGeometry.exists_smooth_maximal_and_image_eq_of_iso_over
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (hdim : ∀ V : X.Opens, Smooth (V.ι ≫ f) → SmoothOfRelativeDimension n (V.ι ≫ f)) :
    ∃ U : X.Opens, SmoothOfRelativeDimension n (U.ι ≫ f) ∧
      (∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → w.hom ''ᵁ U = U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → ∀ (T : Scheme.{u}) (ε : T ⟶ X),
        Set.range ε.base ⊆ (U : Set X) → Set.range (ε ≫ w.hom).base ⊆ (U : Set X)) := by sorry
