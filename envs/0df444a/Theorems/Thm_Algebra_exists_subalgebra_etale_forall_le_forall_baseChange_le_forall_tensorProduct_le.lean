-- Prove2me | Theorems.Thm_Algebra_exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le
-- name    : Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7cc17e07-ddf0-5ac5-b790-acc7b63a27d3
-- title:
--   Largest étale subalgebra of a finite k-algebra
-- statement:
--   Let $k$ be a field and let $A$ be a commutative $k$-algebra that is finite as a $k$-module. Then there is a $k$-subalgebra $P \subseteq A$ with the following four properties. First, $P$ is étale as a $k$-algebra. Second, every $k$-subalgebra $S \subseteq A$ that is étale over $k$ satisfies $S \le P$, so $P$ is the largest étale $k$-subalgebra of $A$. Third, $P$ remains largest after any extension of the base field: for every field $K$ carrying a $k$-algebra structure (in the same universe as $k$) and every $K$-subalgebra $S \subseteq K \otimes_k A$ which is étale over $K$, one has $S \le$ the range of the map $K \otimes_k P \to K \otimes_k A$ obtained by tensoring the identity of $K$ with the inclusion of $P$ into $A$. Fourth, $P$ is multiplicative in tensor products: for every commutative $k$-algebra $B$ finite as a $k$-module and every $k$-subalgebra $Q \subseteq B$ that is étale over $k$ and contains every étale $k$-subalgebra of $B$, every $k$-subalgebra $S \subseteq A \otimes_k B$ which is étale over $k$ satisfies $S \le$ the range of the map $P \otimes_k Q \to A \otimes_k B$ induced by the two inclusions.
--
--   This is the existence and the base-change and tensor-product compatibility of the maximal étale (maximal separable) subalgebra $\pi_0(A)$ of a finite-dimensional commutative algebra over an arbitrary field, the algebraic counterpart of the scheme of connected components of $\operatorname{Spec} A$. It is used to produce the largest étale quotient-type structure in the Hopf-algebra setting, via [`HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field`](thm.html#HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧

      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧

      (∀ (K : Type u) [Field K] [Algebra k K] (S : Subalgebra K (K ⊗[k] A)),
          Algebra.Etale K S →
            S ≤ (Algebra.TensorProduct.map (AlgHom.id K K) P.val).range) ∧

      (∀ (B : Type v) [CommRing B] [Algebra k B] [Module.Finite k B] (Q : Subalgebra k B),
          Algebra.Etale k Q → (∀ S : Subalgebra k B, Algebra.Etale k S → S ≤ Q) →
          ∀ S : Subalgebra k (A ⊗[k] B), Algebra.Etale k S →
            S ≤ (Algebra.TensorProduct.map P.val Q.val).range) := by sorry
