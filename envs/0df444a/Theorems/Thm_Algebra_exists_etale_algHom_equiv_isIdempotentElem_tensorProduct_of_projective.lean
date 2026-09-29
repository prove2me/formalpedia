-- Prove2me | Theorems.Thm_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
-- name    : Algebra.exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/825337dc-cbda-5803-bbee-9c83fe59fe14
-- title:
--   Idempotents of a finite projective algebra are represented by an étale algebra
-- statement:
--   Let $R$ be a commutative ring and let $Q$ be a commutative $R$-algebra which, as an $R$-module, is finitely generated and projective (both $R$ and $Q$ taken in a fixed universe). The assertion is the existence of a commutative ring $C$, carried in the same universe, together with an $R$-algebra structure on $C$ making it an étale $R$-algebra in the sense of Mathlib's `Algebra.Etale` (formally étale and of finite presentation over $R$), and of a family $\eta$ assigning to every commutative $R$-algebra $S$ in that universe a bijection $$\eta_S \colon \operatorname{Hom}_{R\text{-alg}}(C, S) \;\xrightarrow{\ \sim\ }\; \{\, e \in S \otimes_R Q \;:\; e^2 = e \,\},$$ the target being the subtype of idempotent elements of the base change $S \otimes_R Q$, such that the family is natural: for all commutative $R$-algebras $S$ and $T$, every $R$-algebra homomorphism $g \colon S \to T$ and every $R$-algebra homomorphism $c \colon C \to S$, the underlying element of $S \otimes_R Q$ attached to $c$ by $\eta_S$ is carried by $g \otimes \mathrm{id}_Q$ to the underlying element of $T \otimes_R Q$ attached by $\eta_T$ to the composite of $c$ followed by $g$. Thus the functor $S \mapsto \{e \in S \otimes_R Q : e^2 = e\}$ on commutative $R$-algebras is represented by an étale $R$-algebra.
--
--   This is the affine, algebra-level form of the representability of the functor of open-and-closed subschemes of a finite locally free scheme over a varying base by an étale scheme over the base. It is used in the construction of the étale algebra representing clopen subschemes of a finite étale morphism, via [`AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale`](thm.html#AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e}),
      ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q) := by sorry
