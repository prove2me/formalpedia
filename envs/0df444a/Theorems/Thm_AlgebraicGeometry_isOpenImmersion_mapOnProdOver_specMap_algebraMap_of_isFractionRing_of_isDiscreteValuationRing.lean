-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/1c1828ec-abbe-57bc-a667-b09d7c05bb1a
-- title:
--   Generic fibre of an S-scheme over a DVR is open
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes, let $O$ be a commutative ring that is a domain and a discrete valuation ring, and let $g \colon \operatorname{Spec} O \to S$ be a morphism. Let $T'$ be a field equipped with an $O$-algebra structure that makes it a fraction field of $O$ (i.e. $\operatorname{Frac}(O) \cong T'$ via the structure map), let $gT \colon \operatorname{Spec} T' \to S$ be a morphism, and assume the triangle commutes: the morphism $\operatorname{Spec} T' \to \operatorname{Spec} O$ induced by the structure homomorphism $O \to T'$, followed by $g$, equals $gT$. Under these hypotheses the morphism of fibre products $$\mathcal{C} \times_S \operatorname{Spec} T' \longrightarrow \mathcal{C} \times_S \operatorname{Spec} O$$ produced by `mapOnProdOver`, namely the morphism of pullbacks determined by the identity of $\mathcal{C}$, by $\operatorname{Spec} T' \to \operatorname{Spec} O$, and by the identity of $S$ (compatibility supplied by the commuting triangle), is an open immersion.
--
--   This is the statement that the generic fibre of a scheme over a discrete valuation ring base point sits inside the full base change as an open subscheme, i.e. stability of open immersions under base change applied to $\operatorname{Spec}\operatorname{Frac}(O) \to \operatorname{Spec} O$. It is used in the study of models of the modular curve $X_1(p)$, where ideal sheaves and relative effective Cartier divisors on a model over a discrete valuation ring are compared with their restrictions to the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Spec (CommRingCat.of O) ⟶ S}
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT) :
    IsOpenImmersion (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) := by sorry
