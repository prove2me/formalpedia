-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinrank_unit_zero_eq_one_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/47d4ab04-b12a-5172-a190-79184ca62d5b
-- title:
--   Čech degree-zero rank one for the structure sheaf
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a scheme equipped with a morphism $\pi : V \to \operatorname{Spec} R$ (with $R$ regarded as an object of `CommRingCat`). Via `Scheme.TwoAffineOpenCover.algebraOfHom`, $\pi$ makes each section ring $\Gamma(V, U)$ an $R$-algebra, the structure map being the inverse of the Gamma–Spec isomorphism followed by $\pi$'s induced map $\Gamma(\operatorname{Spec} R, \top) \to \Gamma(V, U)$; the hypothesis is that for $U = \top$ this algebra map $R \to \Gamma(V, \top)$ is bijective. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$, each an affine open, whose supremum is $\top$. Consider the presheaf of modules `OModulePresheaf.unit π`, whose value on an open $U$ is $\Gamma(V, U)$ with its $R$-module and $\Gamma(V,U)$-module structures and whose restriction maps are the restriction maps of the structure sheaf. The conclusion is that `cechFinrank K 0` for this datum equals $1$; by definition of `cechFinrank` in degree $0$, this says that the $R$-module `H0 K` attached to the presheaf and the cover (the degree-zero term of its alternating Čech cohomology) has $R$-rank $1$.
--
--   This is the sheaf axiom for the structure sheaf in Čech degree zero, combined with the rank count $\dim_R R = 1$: an alternating $0$-cochain agreeing on overlaps glues to a unique global section, and global sections are assumed to be exactly $R$. It feeds the Euler-characteristic and rank computations for the structure sheaf, being cited by [`AlgebraicGeometry.Polarisation.finrank_H0_baseChange_residue_sliceAt_stalk_eq_one`](thm.html#AlgebraicGeometry.Polarisation.finrank_H0_baseChange_residue_sliceAt_stalk_eq_one) and [`GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_unit_zero_eq_one_of_bijective
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (h : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap R Γ(V, ⊤)))
    (K : V.OrderedAffineCover) :
    (OModulePresheaf.unit π).cechFinrank K 0 = 1 := by sorry
