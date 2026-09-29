-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
-- name    : AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7b855ac3-ac1f-5bdf-8080-01d1058d5ba8
-- title:
--   Smooth morphisms over Henselian local rings have sections lifting residue points
-- statement:
--   Let $R$ be a commutative ring in a universe $u$ which is a Henselian local ring, with residue field $\kappa =$ `IsLocalRing.ResidueField R`, and let $X$ be a scheme in the same universe. Let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is smooth in Mathlib's sense (the class `Smooth`), and let $x_0 \colon \operatorname{Spec} \kappa \to X$ be a morphism whose composite with $f$, namely $x_0$ followed by $f$, equals the morphism $\operatorname{Spec} \kappa \to \operatorname{Spec} R$ induced by the structure map $R \to \kappa$; that is, $x_0$ is a $\kappa$-valued point of $X$ lying over the closed point of $\operatorname{Spec} R$. The conclusion is that there exists a morphism $s \colon \operatorname{Spec} R \to X$ such that $s$ followed by $f$ is the identity of $\operatorname{Spec} R$, so that $s$ is a section of $f$, and such that the morphism $\operatorname{Spec} \kappa \to \operatorname{Spec} R$ induced by $R \to \kappa$ followed by $s$ equals $x_0$, so that $s$ reduces to the given point $x_0$ on the special fibre.
--
--   This is the form of Hensel's lemma for smooth morphisms: for $f$ smooth over a Henselian local ring $R$ with residue field $\kappa$, the reduction map $X(R) \to X(\kappa)$ hits every $\kappa$-point over the closed point, in particular it is surjective (Bosch–Lütkebohmert–Raynaud §2.3, Proposition 5; EGA IV 18.5.17). It is used in the project to produce $R$-points of smooth schemes over Henselian local rings, for instance in the statements about dense sets of points admitting sections, about sections with prescribed stalk behaviour at the closed point, and about finite étale covers of discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s = x₀ := by sorry
