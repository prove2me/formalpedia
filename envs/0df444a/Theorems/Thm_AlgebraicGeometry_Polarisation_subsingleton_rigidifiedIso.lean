-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso
-- name    : AlgebraicGeometry.Polarisation.subsingleton_rigidifiedIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/e39e1cc4-ae3d-570c-8478-8d45a547ed19
-- title:
--   Uniqueness of rigidified isomorphisms of invertible modules
-- statement:
--   Let $T$ be a commutative ring, $B$ a scheme and $h : B \to \operatorname{Spec} T$ a morphism of schemes, and assume that the ring homomorphism $T \to \Gamma(B, \mathcal{O}_B)$ obtained as the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} T) \cong T$ followed by the map induced by $h$ on global sections is bijective. Let $e : \operatorname{Spec} T \to B$ be a section of $h$, i.e. $e$ followed by $h$ is the identity of $\operatorname{Spec} T$. Let $M$ and $M'$ be sheaves of modules on $B$, and suppose $M$ is invertible in the sense that every point of $B$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow B$ is isomorphic to the unit module (the structure sheaf) of $U$. Suppose given rigidifications, that is, isomorphisms $\alpha : e^{*}M \cong \mathcal{O}_{\operatorname{Spec} T}$ and $\alpha' : e^{*}M' \cong \mathcal{O}_{\operatorname{Spec} T}$ of the pullbacks along $e$ with the unit module on $\operatorname{Spec} T$. The conclusion is that the type of pairs consisting of an isomorphism $\varphi : M \cong M'$ of modules on $B$ together with the condition that $e^{*}\varphi$ followed by $\alpha'$ equals $\alpha$ is a subsingleton: any two such rigidified isomorphisms coincide. No assertion of existence is made, and no invertibility of $M'$ is assumed.
--
--   This is the rigidity statement underlying the representability of relative Picard functors by rigidified line bundles: when the base ring maps isomorphically onto the global functions of $B$, a trivialisation along a section of $h$ pins down an isomorphism of invertible modules uniquely. It is used in the construction of rigidified line bundles from local data, where it supplies the uniqueness half of the corresponding existence-and-uniqueness statement, and it rests on the fact that every endomorphism of an invertible module is multiplication by a unique global section, as recorded in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.subsingleton_rigidifiedIso
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ h.appTop).hom)
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) :
    Subsingleton {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} := by sorry
