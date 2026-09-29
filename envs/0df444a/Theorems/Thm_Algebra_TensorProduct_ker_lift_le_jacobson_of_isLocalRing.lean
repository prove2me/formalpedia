-- Prove2me | Theorems.Thm_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing
-- name    : Algebra.TensorProduct.ker_lift_le_jacobson_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5c240246-9c63-5bd2-97e5-65fa81a75080
-- title:
--   Kernel of id_C⊗ε lies in the Jacobson radical
-- statement:
--   Let $R$ be a commutative local ring, let $C$ be a commutative $R$-algebra that is finite as an $R$-module, and let $D$ be a commutative $R$-algebra that is finite as an $R$-module and is itself a local ring. Let $\varepsilon \colon D \to R$ be an $R$-algebra homomorphism. Consider the $R$-algebra homomorphism $f \colon C \otimes_R D \to C$ obtained from the pair consisting of the identity of $C$ and the composite of $\varepsilon$ with the structure map $R \to C$, these two having commuting images since $C$ is commutative; on elementary tensors it sends $c \otimes d$ to $\varepsilon(d)\,c$, so it is the map $\mathrm{id}_C \otimes \varepsilon$ followed by the identification $C \otimes_R R \cong C$. The assertion is that the kernel of $f$ is contained in `Ideal.jacobson ⊥` for the ring $C \otimes_R D$, that is, in the intersection of all maximal ideals of $C \otimes_R D$ (the Jacobson radical). No flatness, separability or Noetherian hypothesis on $R$, $C$ or $D$ is imposed beyond module-finiteness and locality of $R$ and $D$.
--
--   This records that base change along a finite local $R$-algebra $D$ with a section $\varepsilon$ changes nothing modulo the Jacobson radical: $\operatorname{Spec} D \to \operatorname{Spec} R$ behaves like a thickened point, so $C \otimes_R D \to C$ is a bijection on maximal ideals and injective on idempotents. It is used in the construction of the connected–étale sequence of a finite flat group scheme over $\mathbb{Z}_p$, via [`HopfAlgebra.exists_connected_etale_sequence_padicInt`](thm.html#HopfAlgebra.exists_connected_etale_sequence_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.TensorProduct.ker_lift_le_jacobson_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
    {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
    (ε : D →ₐ[R] R) :
    RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) : C ⊗[R] D →ₐ[R] C) ≤ Ideal.jacobson ⊥ := by sorry
