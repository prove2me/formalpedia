-- Prove2me | Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv
-- name    : AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3113d2ae-6679-52b7-b943-fba23eece679
-- title:
--   Base change of L⊗_K A along a bicontinuous ring isomorphism
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite-dimensional $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$. Let $A$ be a commutative topological ring which is a $K$-algebra, and let $A'$ be a commutative topological ring, both with continuous ring operations, and let $e \colon A \to A'$ be a ring isomorphism such that $e$ and $e^{-1}$ are continuous. Give $A'$ the $K$-algebra structure whose structural map is $\mathrm{algebraMap}\colon K \to A$ followed by $e$. Then there exists a ring isomorphism $E \colon L \otimes_K A \to L \otimes_K A'$ (the tensor products carrying the topologies from the scoped `TensorProduct.RightActions` instances) such that: $E$ and $E^{-1}$ are continuous; $E(x \otimes a) = x \otimes e(a)$ for all $x \in L$, $a \in A$; $E$ intertwines the two twists `sigmaTensor`, i.e. the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K A$ and of $L \otimes_K A'$, so $E \circ (\sigma \otimes \mathrm{id}) = (\sigma \otimes \mathrm{id}) \circ E$; and $E$ is compatible with the inclusions `toTensorGL` given entrywise by $a \mapsto 1 \otimes a$, in the sense that applying $E$ entrywise to the image in $\mathrm{GL}_2(L \otimes_K A)$ of $g \in \mathrm{GL}_2(A)$ equals the image in $\mathrm{GL}_2(L \otimes_K A')$ of the matrix obtained from $g$ by applying $e$ entrywise.
--
--   This is the transport of the base-changed coefficient ring $L \otimes_K A$ along an isomorphism of the coefficient ring $A$, recorded together with all the compatibilities needed later: bicontinuity, the pure-tensor formula, the Galois twist $\sigma \otimes \mathrm{id}$, and the entrywise inclusion of $\mathrm{GL}_2$. It is used in the comparison of twisted orbital integrals with orbital integrals at archimedean places, where a completion is identified with $\mathbb{R}$ or $\mathbb{C}$ by such an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (A' : Type) [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm) :
    letI : Algebra K A' := (e.toRingHom.comp (algebraMap K A)).toAlgebra
    ∃ E : L ⊗[K] A ≃+* L ⊗[K] A',
      Continuous E ∧ Continuous E.symm ∧
      (∀ (x : L) (a : A), E (x ⊗ₜ a) = x ⊗ₜ e a) ∧
      (∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) ∧
      (∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
        toTensorGL K L A' (Matrix.GeneralLinearGroup.map e.toRingHom g)) := by sorry
