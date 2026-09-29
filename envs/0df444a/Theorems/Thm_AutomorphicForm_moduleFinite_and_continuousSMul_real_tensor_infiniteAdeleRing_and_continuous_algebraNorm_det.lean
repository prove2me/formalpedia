-- Prove2me | Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
-- name    : AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/dec3b2ab-1f71-51ee-82a8-77892d050944
-- title:
--   Real structure on L⊗_K K_∞: finiteness and continuity
-- statement:
--   Let $K$ and $L$ be number fields and let $L$ be a $K$-algebra. Write $K_\infty$ for the infinite adele ring `InfiniteAdeleRing K` and $E = L \otimes_K K_\infty$. The statement installs two $\mathbb{R}$-algebra structures: on $K_\infty$, the one transported from the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $K$ through the inverse of the canonical ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K`, composed with the structure map of $\mathbb{R}$ into that mixed space; and on $E$, the one obtained from the previous structure map followed by the right inclusion $a \mapsto 1 \otimes a$ of $K_\infty$ into $E$. With these structures the conclusion is a sevenfold conjunction: $\mathbb{R} \to K_\infty \to E$ is a tower of scalars; $K_\infty$ is a finite $\mathbb{R}$-module; $E$ is a finite $\mathbb{R}$-module; the structure map $\mathbb{R} \to K_\infty$ is continuous; scalar multiplication $\mathbb{R} \times E \to E$ is continuous for the topology of $E$; the algebra norm $N_{E/\mathbb{R}} : E \to \mathbb{R}$ is continuous; and the map $M_2(E) \to \mathbb{R}$, $X \mapsto N_{E/\mathbb{R}}(\det X)$, is continuous.
--
--   This packages the archimedean real structure used in the normalisation of Haar measure on a twisted centraliser, where the relevant density on $M_2(E)$ is built from $|N_{E/\mathbb{R}}(\det X)|$: the conjuncts supply the finite-dimensionality, scalar-tower compatibility and continuity (hence measurability) facts that the normalisation requires. It is cited by the computations relating the Gram determinant and the discriminant of $L/K$ to $N_{E/\mathbb{R}}(\det X)$, and by the finiteness statements for the corresponding archimedean integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) ∧
    Module.Finite ℝ (InfiniteAdeleRing K) ∧ Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (algebraMap ℝ (InfiniteAdeleRing K)) ∧
    ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) ∧
    Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => Algebra.norm ℝ X.det) := by sorry
