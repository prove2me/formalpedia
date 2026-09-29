-- Prove2me | Theorems.Thm_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
-- name    : Algebra.Etale.exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/ad82269c-1ba1-52d4-8028-f0debf28133c
-- title:
--   Two points of an étale algebra agree on a distinguished idempotent
-- statement:
--   Let $S$, $B$, $C$ be commutative rings with $B$ and $C$ commutative $S$-algebras, and assume $B$ is étale over $S$ (in Mathlib's sense: formally unramified, formally smooth and of finite presentation). Let $x, y : B \to C$ be two $S$-algebra homomorphisms. Then there exists an element $e \in C$ such that: (i) $e$ is idempotent, $e \cdot e = e$; (ii) $e\,x(b) = e\,y(b)$ for every $b \in B$; (iii) the ring homomorphisms underlying $x$ and $y$ become equal after composing with the structure map $C \to C[1/e]$ into the localisation of $C$ away from $e$, i.e. the two composites $B \to C \to C[1/e]$ coincide; (iv) for every prime ideal $\mathfrak p$ of $C$ one has $e \notin \mathfrak p$ if and only if $x(b) - y(b) \in \mathfrak p$ for all $b \in B$; and (v) for every field $k$ and every ring homomorphism $\chi : C \to k$ with $\chi \circ x = \chi \circ y$ as ring homomorphisms $B \to k$, one has $\chi(e) = 1$.
--
--   This is the standard statement that the locus where two $S$-points of an étale $S$-algebra agree is cut out by an idempotent, equivalently that the diagonal of an étale morphism is an open (and closed) immersion; the idempotent is the image of the separability element. It is used in the construction of the group law on Jacobians of curves with good reduction, where it feeds the production of a finite étale, faithfully flat base change over which prescribed bases exist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
    {S B C : Type} [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C] [Algebra.Etale S B]
    (x y : B →ₐ[S] C) :
    ∃ e : C, IsIdempotentElem e ∧ (∀ b : B, e * x b = e * y b) ∧
      (algebraMap C (Localization.Away e)).comp x.toRingHom = (algebraMap C (Localization.Away e)).comp y.toRingHom ∧
      (∀ 𝔭 : Ideal C, 𝔭.IsPrime → (e ∉ 𝔭 ↔ ∀ b : B, x b - y b ∈ 𝔭)) ∧
      (∀ (k : Type) [Field k] (χ : C →+* k), χ.comp x.toRingHom = χ.comp y.toRingHom → χ e = 1) := by sorry
