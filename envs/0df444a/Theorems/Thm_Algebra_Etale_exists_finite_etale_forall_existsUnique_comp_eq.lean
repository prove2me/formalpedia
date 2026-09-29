-- Prove2me | Theorems.Thm_Algebra_Etale_exists_finite_etale_forall_existsUnique_comp_eq
-- name    : Algebra.Etale.exists_finite_etale_forall_existsUnique_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/9782a4ec-898c-5eb2-bf52-fcfc68260fe7
-- title:
--   An m-fold tensor power classifying m-tuples of points
-- statement:
--   Let $S$ and $B$ be commutative rings with $B$ an $S$-algebra that is finite as an $S$-module and étale over $S$, and let $m$ be a natural number. The assertion is the existence of a commutative ring $C$, carrying an $S$-algebra structure for which $C$ is finite as an $S$-module and étale over $S$, together with a family $u : \mathrm{Fin}\,m \to (B \to_{\mathrm{alg}[S]} C)$ of $S$-algebra homomorphisms $B \to C$ indexed by $\{0,\dots,m-1\}$, with the following universal property: for every commutative ring $D$ equipped with an $S$-algebra structure and every family $v$ of $S$-algebra homomorphisms $v_i : B \to D$ indexed by the same finite set, there is exactly one $S$-algebra homomorphism $w : C \to D$ such that $w \circ u_i = v_i$ for all $i$. Thus $\operatorname{Spec} C$ represents the $m$-fold fibre product of $\operatorname{Spec} B$ over $\operatorname{Spec} S$, together with its universal $m$-tuple of points. The test algebras $D$, like $S$, $B$ and $C$, range over `Type`; no uniqueness is claimed for $C$ itself, and the construction of $C$ is hidden behind the existential quantifier.
--
--   This is the existence, with its universal property, of the $m$-fold tensor power $B^{\otimes_S m}$ of a finite étale algebra, phrased so that users see only the representability statement. It is used in the construction of the relative group law on the Jacobian of a curve of good reduction, where $m$-tuples of points of a finite étale algebra must be split over a single finite étale extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_finite_etale_forall_existsUnique_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.exists_finite_etale_forall_existsUnique_comp_eq
    (S B : Type) [CommRing S] [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B] (m : ℕ) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Module.Finite S C) (_ : Algebra.Etale S C)
      (u : Fin m → (B →ₐ[S] C)),
      ∀ (D : Type) [CommRing D] [Algebra S D] (v : Fin m → (B →ₐ[S] D)),
        ∃! w : C →ₐ[S] D, ∀ i, w.comp (u i) = v i := by sorry
