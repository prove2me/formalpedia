-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage
-- name    : AlgebraicGeometry.Scheme.singleton_sigma_mem_fppfPrecoverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7fce45b5-b37c-5c38-8675-7e309bbfbb1c
-- title:
--   A finite affine fppf family yields a single fppf cover
-- statement:
--   Let $R$ be a commutative ring (an object of `CommRingCat` in universe $u$), let $\iota$ be a finite type in universe $u$, let $A : \iota \to$ `CommRingCat` be a family of commutative rings and let $\varphi_i \colon R \to A_i$ be ring homomorphisms. Assume that the presieve on $\operatorname{Spec} R$ given by the family of arrows $\operatorname{Spec}(\varphi_i) \colon \operatorname{Spec} A_i \to \operatorname{Spec} R$, indexed by $i \in \iota$, lies in the fppf precoverage of $\operatorname{Spec} R$, that is: the maps on underlying topological spaces are jointly surjective and each $\operatorname{Spec}(\varphi_i)$ is flat and locally of finite presentation. Then the singleton presieve consisting of the single morphism $\operatorname{Spec}\bigl(\prod_{i \in \iota} A_i\bigr) \to \operatorname{Spec} R$ induced by the product homomorphism $r \mapsto (\varphi_i(r))_{i \in \iota}$ from $R$ to the product ring $\prod_i A_i$ also lies in the fppf precoverage of $\operatorname{Spec} R$; equivalently, that single morphism is surjective, flat and locally of finite presentation.
--
--   This is the standard refinement step of the fppf topology on affines: a finite affine fppf covering family of an affine scheme can be replaced by one affine fppf cover, namely the spectrum of the product of the covering algebras. It is used in [`AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial`](thm.html#AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial), where descent arguments over an affine base are reduced to a single fppf cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.singleton_sigma_mem_fppfPrecoverage
    {R : CommRingCat.{u}} {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) (φ : ∀ i, R ⟶ A i)
    (h : Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R)) :
    Presieve.singleton (Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom))) ∈
      Scheme.fppfPrecoverage (Spec R) := by sorry
