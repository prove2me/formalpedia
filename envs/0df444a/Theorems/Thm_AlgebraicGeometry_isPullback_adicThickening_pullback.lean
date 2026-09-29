-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_adicThickening_pullback
-- name    : AlgebraicGeometry.isPullback_adicThickening_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c8d7db46-7aa7-57a7-b666-687b806e694d
-- title:
--   Adic thickenings commute with fibre products
-- statement:
--   Let $R$ be a commutative ring, $I \subseteq R$ an ideal, $X$ and $Y$ schemes, $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ morphisms, and $n$ a natural number. Write $B_n = \operatorname{Spec}(R/I^{n+1})$ and let `adicThickeningBase I n` be the morphism $B_n \to \operatorname{Spec} R$ induced by the quotient map $R \to R/I^{n+1}$; for a morphism $h$ to $\operatorname{Spec} R$, `adicThickening h I n` is by definition the fibre product of $h$ with this base morphism, `adicThickeningToBase h I n` its second projection to $B_n$, and `adicThickeningι h I n` the accompanying projection to the source of $h$. Put $p =$ (`pullback.fst f g`) followed by $f$, the structure morphism of $X \times_{\operatorname{Spec} R} Y$ over $\operatorname{Spec} R$. Assume given $\mathrm{pr}_X :$ `adicThickening p I n` $\to$ `adicThickening f I n` such that $\mathrm{pr}_X$ followed by `adicThickeningι f I n` equals `adicThickeningι p I n` followed by `pullback.fst f g`, and $\mathrm{pr}_X$ followed by `adicThickeningToBase f I n` equals `adicThickeningToBase p I n`; and likewise $\mathrm{pr}_Y :$ `adicThickening p I n` $\to$ `adicThickening g I n` compatible with `pullback.snd f g` and with the morphisms to $B_n$. Then the square formed by $\mathrm{pr}_X$, $\mathrm{pr}_Y$, `adicThickeningToBase f I n` and `adicThickeningToBase g I n` is cartesian; in particular the two composites to $B_n$ agree, and $(X \times_{\operatorname{Spec} R} Y)_n$ is the fibre product of $X_n$ and $Y_n$ over $B_n$.
--
--   This is the base-change compatibility of the $I$-adic thickening functor: thickening commutes with fibre products over $\operatorname{Spec} R$. The induced projections are taken as hypotheses pinned by their composites rather than constructed, so that any spelling of the induced morphism may be supplied; the result is used in the analysis of the graph of a morphism of thickenings, in [`AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph`](thm.html#AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_adicThickening_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isPullback_adicThickening_pullback
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (prX : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hprX₁ : prX ≫ adicThickeningι f I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g)
    (hprX₂ : prX ≫ adicThickeningToBase f I n = adicThickeningToBase (pullback.fst f g ≫ f) I n)
    (prY : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening g I n)
    (hprY₁ : prY ≫ adicThickeningι g I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g)
    (hprY₂ : prY ≫ adicThickeningToBase g I n = adicThickeningToBase (pullback.fst f g ≫ f) I n) :
    IsPullback prX prY (adicThickeningToBase f I n) (adicThickeningToBase g I n) := by sorry
