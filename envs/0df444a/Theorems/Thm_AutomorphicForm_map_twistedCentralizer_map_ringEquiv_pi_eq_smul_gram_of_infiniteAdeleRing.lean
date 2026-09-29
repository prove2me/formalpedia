-- Prove2me | Theorems.Thm_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
-- name    : AutomorphicForm.map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/6037954b-65e3-5052-a915-2ee72e811db7
-- title:
--   Transport of the archimedean Gram normalisation along Xi
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\Xi : L\otimes_K \mathrm{InfiniteAdeleRing}\,K \to \prod_{w\mid\infty} L\otimes_K K_w$ be a ring isomorphism onto the product over the infinite places $w$ of $K$ of the tensor products with the completions $w.\mathrm{Completion}$, with $\Xi$ and $\Xi^{-1}$ continuous; each factor $L\otimes_K K_w$ carries a given $\mathbb{R}$-algebra structure, and $\Xi$ is assumed $\mathbb{R}$-homogeneous, $\Xi(r\cdot z)=r\cdot\Xi(z)$, for the $\mathbb{R}$-algebra structure on $L\otimes_K \mathrm{InfiniteAdeleRing}\,K$ obtained by transporting the mixed-space $\mathbb{R}$-algebra structure along `InfiniteAdeleRing.ringEquiv_mixedSpace` and composing with `Algebra.TensorProduct.includeRight`. Let $\delta\in \mathrm{GL}_2(L\otimes_K\mathrm{InfiniteAdeleRing}\,K)$, and let $\tau'$ be a measure, for the Borel $\sigma$-algebra, on the twisted centraliser $\{t \mid t\,\delta\,(\sigma_{\mathrm{GL}}t)^{-1}=\delta\}$, where $\sigma_{\mathrm{GL}}$ is the map of $\mathrm{GL}_2$ induced entrywise by the ring homomorphism `sigmaTensor K L (InfiniteAdeleRing K) σ` attached to $\sigma$. Let $n_2\in\mathbb{N}$, let $e_2 : \mathrm{Fin}\,n_2 \to M_2(L\otimes_K\mathrm{InfiniteAdeleRing}\,K)$, and let $s\in[0,\infty]$. The hypothesis is that the pushforward of $\tau'$ under the inclusion $t\mapsto t$ into $M_2(L\otimes_K\mathrm{InfiniteAdeleRing}\,K)$, with the Borel structure, equals $s$ times the measure obtained from $\sqrt{\bigl|\det\bigl(\mathrm{Tr}_{(L\otimes_K\mathrm{InfiniteAdeleRing}\,K)/\mathbb{R}}\,\mathrm{tr}(e_2(i)e_2(j))\bigr)_{i,j}\bigr|}$ times the pushforward of Lebesgue measure under $c\mapsto\sum_i c_i\, e_2(i)$, weighted by the density $X\mapsto |N_{(L\otimes_K\mathrm{InfiniteAdeleRing}\,K)/\mathbb{R}}(\det X)|^{-1}$. The conclusion is the same identity transported by $\Xi$: the pushforward of $\tau'$ under $t\mapsto$ (entrywise $\Xi$ applied to the matrix of $t$) equals $s$ times the analogous measure built from the family $\Xi(e_2(i))$, the Gram determinant of the trace form of $\prod_w L\otimes_K K_w$ over $\mathbb{R}$, and the density $X\mapsto |N_{(\prod_w L\otimes_K K_w)/\mathbb{R}}(\det X)|^{-1}$, on $M_2(\prod_w L\otimes_K K_w)$ with its Borel structure.
--
--   This is the archimedean transport step in the common Gram normalisation of measures on twisted centralisers: the normalisation of $\tau'$ is carried from $L\otimes_K \mathbb{A}_{K,\infty}$ to the product of the local algebras $L\otimes_K K_w$ over the infinite places. It is used by [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom) in the comparison of twisted orbital integrals with ordinary ones at the archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal)
    (hL :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
        s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
              Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
              (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) := borel _
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
    Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) τ' =
      s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
              Algebra.trace ℝ ((w : InfinitePlace K) → L ⊗[K] w.Completion)
                (Matrix.trace ((e₂ i).map Ξ * (e₂ j).map Ξ))).det|)) •
            Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • (e₂ i).map Ξ) volume).withDensity
          (fun X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion) =>
            (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by sorry
