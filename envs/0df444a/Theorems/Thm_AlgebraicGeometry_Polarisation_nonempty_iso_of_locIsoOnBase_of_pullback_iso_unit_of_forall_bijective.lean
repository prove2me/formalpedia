-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f06d39bb-dbad-593c-a9f6-6ed99e151f54
-- title:
--   Invertible modules locally isomorphic over the base and trivialised along a section
-- statement:
--   Let $T$ be a commutative ring, $B$ a scheme, and $h : B \to \operatorname{Spec} T$ a quasi-compact, quasi-separated morphism. Assume the universal global-sections hypothesis: for every commutative $T$-algebra $T'$, the structure map of $T'$-algebras $T' \to \Gamma(B \times_{\operatorname{Spec} T} \operatorname{Spec} T', \top)$ is bijective, where the target carries the $T'$-algebra structure coming from the second projection of the fibre product (the base change being along $\operatorname{Spec}$ of $T \to T'$). Let $e : \operatorname{Spec} T \to B$ be a section of $h$, i.e. $e$ followed by $h$ is the identity. Let $M, M'$ be modules on $B$ (objects of `B.Modules`), each invertible in the sense that every point of $B$ has an open neighbourhood $U$ whose pullback of the module along the inclusion $U \hookrightarrow B$ is isomorphic to the unit sheaf of modules on $U$. Assume `LocIsoOnBase h M M'`: every point of $\operatorname{Spec} T$ lies in an open $U$ such that the pullbacks of $M$ and $M'$ along $h^{-1}U \hookrightarrow B$ are isomorphic. Assume further isomorphisms $\alpha : e^*M \cong \mathcal O$ and $\alpha' : e^*M' \cong \mathcal O$ onto the unit sheaf of modules on $\operatorname{Spec} T$. Then the type of isomorphisms $M \cong M'$ is nonempty.
--
--   This is the existence half of the rigidified see-saw statement for invertible modules: two invertible modules that agree locally on the base and are both trivialised along a section of the base are globally isomorphic, under the hypothesis that forming global sections commutes with base change in the strongest form ($\Gamma = T'$ universally). It feeds the construction of rigidified line bundles and polarisations, being used for the uniqueness-and-existence statement for rigidified isomorphisms and for the triviality of a pullback along the unit section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
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
    Nonempty (M ≅ M') := by sorry
