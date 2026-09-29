-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop
-- name    : AlgebraicGeometry.geometricallyConnected_of_isProper_of_bijective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/65e61a12-df64-5c17-86ca-955b3c13eaf2
-- title:
--   Zariski connectedness: Stein proper morphisms are geometrically connected
-- statement:
--   Let $A$ be a commutative ring in universe $u$ which is Noetherian, let $X$ be a scheme, and let $f \colon X \to \operatorname{Spec} A$ be a morphism of schemes which is proper (the Mathlib class `IsProper`). Assume `hf`: the induced map on global sections, $f$`.appTop` $\colon \Gamma(\operatorname{Spec} A, \mathcal{O}) \to \Gamma(X, \mathcal{O}_X)$, is bijective as a function; here the source is the ring of global sections of the structure sheaf of $\operatorname{Spec} A$, canonically identified with $A$, so the hypothesis says that $f$ coincides with its own Stein factorisation. Under these assumptions the conclusion is `GeometricallyConnected f`, the Mathlib predicate asserting that $f$ is geometrically connected, i.e. that connectedness of $f$ persists after base change along arbitrary field-valued points of $\operatorname{Spec} A$.
--
--   This is Zariski's connectedness theorem in the global, Stein-factorisation form of EGA III, Corollaire 4.3.4, over a Noetherian affine base and phrased in terms of global sections. It is used to upgrade connectedness of a single (special) fibre to connectedness of all geometric fibres, and is cited by [`AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`](thm.html#AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyConnected_of_isProper_of_bijective_appTop
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (hf : Function.Bijective f.appTop) :
    GeometricallyConnected f := by sorry
