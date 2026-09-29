-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective
-- name    : AlgebraicGeometry.Polarisation.nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/9254badc-a864-5474-950a-3350335f5da1
-- title:
--   Unique rigidified isomorphism of locally base-isomorphic invertible modules
-- statement:
--   Let $T$ be a commutative ring, $B$ a scheme and $h : B \to \operatorname{Spec} T$ a quasi-compact, quasi-separated morphism. Assume that for every $T$-algebra $T'$ the map $T' \to \Gamma(B \times_{\operatorname{Spec} T} \operatorname{Spec} T', \top)$, namely the algebra map attached by `Scheme.TwoAffineOpenCover.algebraOfHom` to the second projection of the pullback of $h$ along $\operatorname{Spec}$ of $T \to T'$, is bijective. Let $e : \operatorname{Spec} T \to B$ satisfy $e$ followed by $h$ equals the identity, i.e. $e$ is a section of $h$. Let $M, M'$ be sheaves of modules on $B$, each invertible in the sense that every point of $B$ has an open neighbourhood $U$ for which the pullback along the inclusion $U \hookrightarrow B$ is isomorphic to the unit sheaf of modules, and assume `LocIsoOnBase h M M'`: every point $s$ of $\operatorname{Spec} T$ lies in an open $U$ such that the pullbacks of $M$ and of $M'$ along the inclusion $h^{-1}U \hookrightarrow B$ are isomorphic. Finally let $\alpha : e^*M \cong \mathcal{O}$ and $\alpha' : e^*M' \cong \mathcal{O}$ be isomorphisms onto the unit sheaf of modules on $\operatorname{Spec} T$. Then the type of isomorphisms $\varphi : M \cong M'$ such that $e^*\varphi$ followed by $\alpha'$ equals $\alpha$ is nonempty and is a subsingleton.
--
--   This is the rigidity statement for rigidified invertible sheaves on a scheme over $\operatorname{Spec} T$ with a section and with universally bijective degree-zero global sections: a rigidified isomorphism, if it exists, is unique, and local isomorphy over the base suffices for existence. It underlies the construction of the relative Picard group used for polarisations, being cited for the cocycle relation for rigidified isomorphisms, for descent of local isomorphy along faithfully flat base change with a section, and for the doubling statement on invertible modules with $M \otimes M$ and $-M$ locally trivial on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T)) [QuasiCompact h] [QuasiSeparated h]
    (hH0 : ∀ (T' : Type u) [CommRing T'] [Algebra T T'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd h (Scheme.TwoAffineOpenCover.specMap T T')) ⊤
      Function.Bijective (algebraMap T' Γ(pullback h (Scheme.TwoAffineOpenCover.specMap T T'), ⊤)))
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hloc : LocIsoOnBase h M M')
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) :
    Nonempty {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} ∧
      Subsingleton {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} := by sorry
