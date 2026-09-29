-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_iso_hom_fst_eq_sliceAt_addMor
-- name    : AlgebraicGeometry.Polarisation.exists_iso_hom_fst_eq_sliceAt_addMor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/3f930d46-8c09-5011-9c98-0baa16a34779
-- title:
--   Shear automorphism (a,y)↦(a+j(y),y) of A×_k Y
-- statement:
--   Let $k$ be a field (in the bottom universe), let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: for every test scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the unit laws, left inversion, and naturality of the multiplication under base change along any $\psi : T' \to T$ with $\psi \circ t = t'$. Let $Y$ be a scheme with $f_Y : Y \to \operatorname{Spec} k$ and $j : Y \to A$ a morphism over $k$, i.e. $j \circ f = f_Y$. The conclusion asserts the existence of an isomorphism $\Phi$ of the fibre product $A \times_{\operatorname{Spec} k} Y$ (the pullback of $f$ along $f_Y$) with itself such that $\Phi \circ \mathrm{pr}_2 = \mathrm{pr}_2$ and $\Phi$ followed by $\mathrm{pr}_1$ equals `sliceAt f ⟨j, hjf⟩ ≫ addMor f L`, i.e. the composite of the morphism $A\times_k Y \to A \times_k A$ with components $(\mathrm{pr}_1, \mathrm{pr}_2 \circ j)$ with the addition morphism $A\times_k A \to A$ obtained by multiplying the two projections, viewed as points over $\mathrm{pr}_1 \circ f$. Informally, $\Phi(a,y) = (a + j(y), y)$.
--
--   This is the classical shear automorphism of $A \times Y$ attached to a morphism $j : Y \to A$ into a scheme with a group law, which for $Y = A$ and $j = \mathrm{id}$ is the map $(x,y) \mapsto (x+y,y)$ used in the theory of abelian varieties. It is invoked in the polarisation and Rosati involution development, where a Künneth-type absorption argument needs to replace a morphism out of $A \times_k Y$ by its shear.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_iso_hom_fst_eq_sliceAt_addMor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_iso_hom_fst_eq_sliceAt_addMor
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) (hjf : j ≫ f = fY) :
    ∃ Φ : pullback f fY ≅ pullback f fY,
      Φ.hom ≫ pullback.fst f fY = sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) ≫ addMor f L ∧
      Φ.hom ≫ pullback.snd f fY = pullback.snd f fY := by sorry
