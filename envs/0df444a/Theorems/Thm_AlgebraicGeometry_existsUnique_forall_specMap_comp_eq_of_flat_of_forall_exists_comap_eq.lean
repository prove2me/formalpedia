-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
-- name    : AlgebraicGeometry.existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/4c48625f-044e-5401-bcc4-78ef1644d0c2
-- title:
--   fpqc descent of morphisms to a scheme along a finite flat cover
-- statement:
--   Let $B$ be a commutative ring and let $\iota$ be a finite index type. For each $i \in \iota$ let $B'_i$ be a commutative ring equipped with a $B$-algebra structure making $B'_i$ flat as a $B$-module. Assume the family is jointly surjective on spectra: every prime $\mathfrak p$ of $B$ is the preimage, under some structure map $B \to B'_i$, of a prime $\mathfrak q$ of $B'_i$, i.e. $\mathfrak p$ is the image of $\mathfrak q$ under the map $\operatorname{Spec} B'_i \to \operatorname{Spec} B$ induced by $\operatorname{algebraMap}$. Let $T$ be a scheme and, for each $i$, let $\varphi'_i \colon \operatorname{Spec} B'_i \to T$ be a morphism of schemes. Assume the $\varphi'_i$ agree on the pairwise overlaps in the sense that, for all $i, j$, the morphism $\operatorname{Spec}(B'_i \otimes_B B'_j) \to \operatorname{Spec} B'_i$ induced by the left inclusion $b \mapsto b \otimes 1$, followed by $\varphi'_i$, equals the morphism $\operatorname{Spec}(B'_i \otimes_B B'_j) \to \operatorname{Spec} B'_j$ induced by the right inclusion $b \mapsto 1 \otimes b$, followed by $\varphi'_j$. Then there is a unique morphism of schemes $\varphi \colon \operatorname{Spec} B \to T$ such that for every $i$ the morphism $\operatorname{Spec} B'_i \to \operatorname{Spec} B$ induced by $B \to B'_i$, followed by $\varphi$, equals $\varphi'_i$.
--
--   This is the statement that a representable functor on schemes is a sheaf for the fpqc topology, in the concrete form of descent of $T$-valued points along a finite family of flat $B$-algebras that is jointly surjective on spectra (rather than along a single faithfully flat algebra). It is used in the construction of the Čerednik–Drinfel'd uniformisation to produce the unique morphism from an affine base factoring a compatible family of morphisms out of a fine moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
    {B : Type u} [CommRing B] {ι : Type u} [Finite ι]
    (B' : ι → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra B (B' i)] [∀ i, Module.Flat B (B' i)]
    (hcov : ∀ 𝔭 : PrimeSpectrum B, ∃ (i : ι) (𝔮 : PrimeSpectrum (B' i)), PrimeSpectrum.comap (algebraMap B (B' i)) 𝔮 = 𝔭)
    {T : Scheme.{u}} (φ' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ T)
    (h : ∀ i j, Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' i →+* B' i ⊗[B] B' j)) ≫ φ' i =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' j →ₐ[B] B' i ⊗[B] B' j).toRingHom) ≫ φ' j) :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, ∀ i, Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ = φ' i := by sorry
