-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
-- name    : Algebra.FormallySmooth.formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/95f99050-3576-582b-bb39-24d49d739268
-- title:
--   Étale coordinate: A[X]→ S, X↦ t, when dt is a basis
-- statement:
--   Let $A$ and $S$ be commutative rings with $S$ an $A$-algebra which is formally smooth over $A$, and let $t \in S$. Assume that $t$ is an étale coordinate in the differential sense: for every $\omega$ in the module of Kähler differentials $\Omega_{S/A}$ there is exactly one $s \in S$ with $\omega = s \cdot \mathrm{d}_{A/S}t$, where $\mathrm{d}$ denotes `KaehlerDifferential.D A S`; equivalently, $\mathrm{d}t$ is a basis of $\Omega_{S/A}$ as an $S$-module. The conclusion is about the $A$-algebra homomorphism $\mathrm{aeval}\,t : A[X] \to S$ sending $X$ to $t$ (and $a \mapsto a$ on constants): its underlying ring homomorphism is both formally smooth and formally unramified in the sense of `RingHom.FormallySmooth` and `RingHom.FormallyUnramified`, i.e. $S$ is formally smooth and formally unramified over $A[X]$ for the algebra structure induced by $X \mapsto t$. The two assertions together say that this homomorphism is formally étale.
--
--   This is the algebraic form of the statement that a smooth algebra in which some element has a basic differential is étale over the polynomial algebra on that element, an étale coordinate at a smooth point (EGA IV 17.11.4). It is used in the construction of an étale coordinate in [`Algebra.FormallySmooth.exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one`](thm.html#Algebra.FormallySmooth.exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one), where the module of differentials has rank one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u v

theorem Algebra.FormallySmooth.formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (ht : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified := by sorry
