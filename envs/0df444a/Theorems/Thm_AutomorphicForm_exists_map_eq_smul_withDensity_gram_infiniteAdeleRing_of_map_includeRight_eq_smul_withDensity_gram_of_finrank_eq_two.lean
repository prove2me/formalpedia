-- Prove2me | Theorems.Thm_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
-- name    : AutomorphicForm.exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9c5a2914-ba0c-5de7-89a2-079aa545e566
-- title:
--   Gram-normalised measure on M₂(L⊗_K K_∞) descends to M₂(K_∞)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\mathrm{finrank}_K L = 2$, write $K_\infty$ for the infinite adele ring of $K$, and give $K_\infty$ the $\mathbb{R}$-algebra structure transported from the mixed space of $K$ along `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $L \otimes_K K_\infty$ the $\mathbb{R}$-algebra structure obtained by composing this with `Algebra.TensorProduct.includeRight`. All measures are taken for the Borel $\sigma$-algebras of the ambient topologies, $\mathrm{GL}_2$ being equipped with `glBorelOf`, the Borel structure of its topology. Let $\mu$ be a measure on $\mathrm{GL}_2(K_\infty)$, let $n \in \mathbb{N}$, let $e : \mathrm{Fin}\,n \to M_2(L \otimes_K K_\infty)$, and let $s \in [0,\infty]$. Assume: $e$ is $\mathbb{R}$-linearly independent; the $\mathbb{R}$-span of the range of $e$ is exactly the image of $M_2(K_\infty)$ under entrywise application of $\mathrm{includeRight}$; and the pushforward of $\mu$ along $t \mapsto$ (the underlying matrix of $t$, mapped entrywise by $\mathrm{includeRight}$) equals $s$ times the measure obtained from Lebesgue measure on $\mathrm{Fin}\,n \to \mathbb{R}$ pushed forward along $c \mapsto \sum_i c_i e_i$, scaled by $\sqrt{|\det(\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb{R}}\,\mathrm{tr}(e_i e_j))_{i,j}|}$, with density $X \mapsto |N_{(L\otimes_K K_\infty)/\mathbb{R}}(\det X)|^{-1}$. Then there exists $e' : \mathrm{Fin}\,n \to M_2(K_\infty)$ that is $\mathbb{R}$-linearly independent with $\mathbb{R}$-span all of $M_2(K_\infty)$, such that the pushforward of $\mu$ along the inclusion $\mathrm{GL}_2(K_\infty) \to M_2(K_\infty)$ equals $2^{2\,\mathrm{finrank}_{\mathbb{Q}} K} \cdot s$ times the corresponding intrinsic measure for $e'$: Lebesgue measure pushed forward along $c \mapsto \sum_i c_i e'_i$, scaled by $\sqrt{|\det(\mathrm{Tr}_{K_\infty/\mathbb{R}}\,\mathrm{tr}(e'_i e'_j))_{i,j}|}$, with density $Y \mapsto |N_{K_\infty/\mathbb{R}}(\det Y)|^{-2}$.
--
--   This is the archimedean comparison of measure normalisations for a quadratic extension: a Gram-normalised measure on $M_2(L \otimes_K K_\infty)$ supported on the image of $M_2(K_\infty)$ is identified with the intrinsic Gram-normalised measure of $M_2(K_\infty)$, the Haar-type density $|N(\det)|^{-1}$ becoming $|N(\det)|^{-2}$ and the total mass acquiring the factor $4^{[K:\mathbb{Q}]}$ coming from $\mathrm{Tr}_{(L\otimes_K K_\infty)/\mathbb{R}} = 2\,\mathrm{Tr}_{K_\infty/\mathbb{R}}$ on $K_\infty$. It is used in the comparison of fundamental-domain volumes for twisted centralisers in the quadratic base-change computation for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2)
    (μ : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal)
    (h :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        (Submodule.span ℝ (Set.range e) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
            Y.map (Algebra.TensorProduct.includeRight :
              InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) μ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
    letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
    ∃ e' : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K),
      LinearIndependent ℝ e' ∧
        Submodule.span ℝ (Set.range e') = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) μ =
          (2 ^ (2 * Module.finrank ℚ K) * s) •
            ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e' i * e' j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e' i) volume).withDensity
              (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det Y)| ^ 2)⁻¹) := by sorry
