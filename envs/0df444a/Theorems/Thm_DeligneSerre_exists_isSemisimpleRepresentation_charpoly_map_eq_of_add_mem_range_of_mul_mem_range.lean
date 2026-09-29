-- Prove2me | Theorems.Thm_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
-- name    : DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/1499ca2c-08a7-5751-b5d9-00d12e510243
-- title:
--   Deligne–Serre descent of χ₁⊕χ₂ to a finite field
-- statement:
--   Let $G$ be a group, $\kappa$ a finite field, $\Omega$ a field, and $\iota \colon \kappa \to \Omega$ a ring homomorphism. Let $\chi_1, \chi_2 \colon G \to \Omega^{\times}$ be group homomorphisms, and assume that for every $g \in G$ both $\chi_1(g) + \chi_2(g)$ and $\chi_1(g)\,\chi_2(g)$, viewed in $\Omega$, lie in the image of $\iota$. Then there exists a group homomorphism $\rho \colon G \to \mathrm{GL}_2(\kappa)$ with the following three properties. First, the associated representation of $G$ on $\kappa^2$, namely [`Deformation.matrixRepresentation ρ`](def/Deformations_MatrixRepresentation.html#L15), obtained by composing $\rho$ with the identification of $\mathrm{GL}_2(\kappa)$ with invertible $\kappa$-linear endomorphisms of $\mathrm{Fin}\,2 \to \kappa$, is semisimple. Second, for every $g \in G$ with $\chi_1(g) = 1$ and $\chi_2(g) = 1$ one has $\rho(g) = 1$. Third, for every $g \in G$, the characteristic polynomial of the matrix in $M_2(\Omega)$ obtained by applying $\iota$ entrywise to the matrix underlying $\rho(g)$ equals $(X - \chi_1(g))(X - \chi_2(g))$.
--
--   This is the reducible case of Lemme 6.13 of Deligne–Serre: a sum of two characters with values in a field $\Omega$, whose traces and determinants lie in a finite subfield $\iota(\kappa)$, is realised over $\kappa$ by a semisimple two-dimensional representation with the same characteristic polynomials. It feeds the construction of residual Galois representations with prescribed Frobenius characteristic polynomials, being cited by [`GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`](thm.html#GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
    {G : Type} [Group G] {κ : Type} [Field κ] [Finite κ] {Ω : Type} [Field Ω]
    (ι : κ →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g : G, (χ₁ g : Ω) + χ₂ g ∈ ι.range) (hmul : ∀ g : G, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ ρ : G →* GL (Fin 2) κ,
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      (∀ g : G, χ₁ g = 1 → χ₂ g = 1 → ρ g = 1) ∧
      ∀ g : G, (((ρ g : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        (X - C (χ₁ g : Ω)) * (X - C (χ₂ g : Ω)) := by sorry
