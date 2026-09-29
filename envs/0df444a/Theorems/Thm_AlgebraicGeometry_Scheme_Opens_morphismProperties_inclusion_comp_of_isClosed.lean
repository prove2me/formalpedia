-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed
-- name    : AlgebraicGeometry.Scheme.Opens.morphismProperties_inclusion_comp_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b6e3e824-4dee-5fe8-8e97-1e18edf242fa
-- title:
--   Clopen open subscheme inherits the five relative properties
-- statement:
--   Let $B$ be a commutative ring, let $X$ be a scheme, and let $\pi_X : X \to \operatorname{Spec} B$ be a morphism of schemes to the spectrum of $B$ (the ring $B$ viewed as an object of `CommRingCat`). Let $U$ be an open subscheme of $X$ whose underlying set is closed in $X$, and write $U.\iota : U \to X$ for the canonical open immersion. The assertion is a conjunction of five implications, each transferring a property of $\pi_X$ to the composite $U.\iota$ followed by $\pi_X$, i.e. to the restriction $U \to \operatorname{Spec} B$: if $\pi_X$ is separated then so is the composite; if $\pi_X$ is quasi-compact then so is the composite; if $\pi_X$ is locally of finite type then so is the composite; if $\pi_X$ is flat then so is the composite; and if $\pi_X$ is smooth of relative dimension $1$ then so is the composite. All five are stated in the form of implications between the corresponding Mathlib morphism properties rather than as instances.
--
--   This is the routine statement that an open subscheme with closed underlying set (so that its inclusion is both an open and a closed immersion) inherits separatedness, quasi-compactness, local finiteness of type, flatness and smoothness of relative dimension one over the base. It is used for the raised-level coarse moduli scheme, which arises as a clopen locus inside a finite quotient, in [`CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne) and in [`CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne`](thm.html#CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.Opens.morphismProperties_inclusion_comp_of_isClosed
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B))
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    (IsSeparated πX → IsSeparated (U.ι ≫ πX)) ∧ (QuasiCompact πX → QuasiCompact (U.ι ≫ πX)) ∧
      (LocallyOfFiniteType πX → LocallyOfFiniteType (U.ι ≫ πX)) ∧ (Flat πX → Flat (U.ι ≫ πX)) ∧
      (SmoothOfRelativeDimension 1 πX → SmoothOfRelativeDimension 1 (U.ι ≫ πX)) := by sorry
