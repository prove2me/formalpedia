-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
-- name    : AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/711235ae-a606-56f7-971c-97b0776b22d3
-- title:
--   Finiteness of the archimedean zeta integral over a twisted centraliser
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$ and $\delta \in \mathrm{GL}_2(E)$. The twisted centraliser is the subgroup of $t \in \mathrm{GL}_2(E)$ with $t\,\delta\,(\sigma_{\mathrm{GL}} t)^{-1} = \delta$, where $\sigma_{\mathrm{GL}}$ is the automorphism of $\mathrm{GL}_2(E)$ induced entrywise by $\sigma \otimes \mathrm{id}$; it carries its Borel $\sigma$-algebra. Let $\tau_a$ be a measure on it, $s \in [0,\infty]$ with $s \neq \infty$, and $G : M_2(E) \to [0,\infty]$ Borel measurable. Here $\mathbb{A}_{K,\infty}$ is made an $\mathbb{R}$-algebra through its identification with the mixed space of $K$, and $E$ an $\mathbb{R}$-algebra through the right inclusion; $M_2(E)$ carries the Borel $\sigma$-algebra. The assertion: for every $n_2$ and every $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(E)$ such that the image of $\tau_a$ under $t \mapsto t$ (viewed in $M_2(E)$) equals $s$ times the measure obtained from $\sqrt{|\det(\mathrm{Tr}_{E/\mathbb{R}}\,\mathrm{tr}(e_2(i)e_2(j)))_{i,j}|}$ times the pushforward of Lebesgue measure on $\mathbb{R}^{n_2}$ along $c \mapsto \sum_i c_i e_2(i)$, given the density $X \mapsto |N_{E/\mathbb{R}}(\det X)|^{-1}$, and for all real $s_1 \geq 1$, $r$, $C$ with $n_2 + 2\,\dim_{\mathbb{R}} E\,(s_1-1) < r$ and $G(\sum_i c_i e_2(i)) \leq C(1+\|c\|)^{-r}$ for all $c \in \mathbb{R}^{n_2}$, one has $\int^{-} G(t)\,|N_{E/\mathbb{R}}(\det t)|^{s_1}\,d\tau_a(t) < \infty$.
--
--   This is the convergence statement for the archimedean factor of a zeta integral over a twisted centraliser, under the Gram-determinant normalisation of the measure on that group: polynomial decay of order $r$ along the chosen $\mathbb{R}$-frame of $M_2(E)$, beyond the threshold $n_2 + 2\dim_{\mathbb{R}}E\,(s_1-1)$, forces finiteness of the integral twisted by $|N_{E/\mathbb{R}}(\det)|^{s_1}$. It is used in the derivation of the corresponding finiteness for indicator-type test functions on the twisted centraliser in the rank-two case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ))
    (s : ℝ≥0∞) (hs : s ≠ ⊤)
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) →
      ∀ s₁ : ℝ, 1 ≤ s₁ → ∀ (r C : ℝ),
        (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s₁ - 1) < r →
        (∀ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖c‖) ^ (-r))) →
        ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa < ⊤ := by sorry
