-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
-- name    : AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/edbce40a-a9c2-5d76-9c2e-7493cd26a5b9
-- title:
--   Fibrewise flatness criterion for an S-endomorphism
-- statement:
--   Let $S$ and $X$ be schemes and let $f \colon X \to S$ be a morphism of schemes which is flat and locally of finite presentation. Let $h \colon X \to X$ be a morphism over $S$, in the sense that $h$ followed by $f$ equals $f$. For a point $s$ of $S$ let $\mathrm{Spec}\,\kappa(s) \to S$ be the canonical morphism from the residue field of $s$ and form the pullback $X \times_S \mathrm{Spec}\,\kappa(s)$; the endomorphism `schemeFibreEndo f h hh s` of this pullback is the morphism into it determined by the two compatible projections, namely the first projection followed by $h$ together with the second projection (the required compatibility being exactly the relation $h \circ f^{-1}$-side identity $h$ followed by $f$ equals $f$ combined with the pullback condition). Assume that for every point $s$ of $S$ this induced endomorphism of the fibre is flat. Then $h$ is flat as a morphism of schemes.
--
--   This is the implication from fibrewise flatness to flatness in the critère de platitude par fibres over an arbitrary base (EGA IV$_3$ 11.3.11), specialised to the case in which source and target coincide and $h$ is an endomorphism of $X$ over $S$; no Noetherian hypothesis on $S$ is required, the local algebra input being the flatness criterion over residue fields for algebras of finite presentation. It is used in the treatment of relative group laws and Weierstrass models to show that multiplication by $n$, and the associated kernel morphisms, are flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
    {S X : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (h : X ⟶ X) (hh : h ≫ f = f)
    (hfib : ∀ s : S, Flat (schemeFibreEndo f h hh s)) :
    Flat h := by sorry
