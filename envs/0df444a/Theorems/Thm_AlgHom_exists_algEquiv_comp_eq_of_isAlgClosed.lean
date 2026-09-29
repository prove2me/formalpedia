-- Prove2me | Theorems.Thm_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed
-- name    : AlgHom.exists_algEquiv_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/895e55d4-3ff5-562f-a1bd-8b9492e0baeb
-- title:
--   Transitivity of Aut_K(Ω) on K-embeddings into Ω
-- statement:
--   Let $K$ be a field and let $\Omega$ be a field equipped with a $K$-algebra structure such that $\Omega$ is algebraically closed and algebraic over $K$ (that is, $\Omega$ is an algebraic closure of $K$). Let $M$ be a further field with a $K$-algebra structure, of arbitrary transcendence behaviour a priori, and let $\sigma, \tau : M \to \Omega$ be two $K$-algebra homomorphisms. The assertion is that there exists a $K$-algebra automorphism $\gamma$ of $\Omega$ such that the composite of $\sigma$ with $\gamma$, as a $K$-algebra homomorphism $M \to \Omega$, equals $\tau$; the equality is of $K$-algebra homomorphisms, $\gamma \circ \sigma = \tau$. Equivalently, the group $\operatorname{Aut}_K(\Omega)$ acts transitively on the set $\operatorname{Hom}_K(M, \Omega)$, whenever the latter is non-empty. Note that no finiteness, separability or normality hypothesis is imposed on $M/K$, and that the existence of at least one embedding is not asserted: the statement is purely about conjugacy of two given embeddings.
--
--   This is the classical conjugacy of embeddings into an algebraic closure: the absolute Galois group, or more generally $\operatorname{Aut}_K(\bar K)$, acts transitively on the $K$-embeddings of any field extension into $\bar K$. It is used in the treatment of points of modular curves over algebraically closed fields, where it supplies the Galois-descent step in locating places with prescribed specialisation behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.lean

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgHom.exists_algEquiv_comp_eq_of_isAlgClosed
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {M : Type*} [Field M] [Algebra K M] (σ τ : M →ₐ[K] Ω) :
    ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by sorry
