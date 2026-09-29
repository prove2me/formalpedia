-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
-- name    : AutomorphicForm.exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/81c7bf31-c3f4-5e2c-9853-635594b01bef
-- title:
--   Archimedean covolume identity for a twisted commutant
-- statement:
--   Let $K\subseteq L$ be number fields, $\sigma$ a $K$-algebra automorphism of $L$, $\delta_0\in \mathrm{GL}_2(L)$, $c$ a unit of $L\otimes_K\mathbb{A}_K$, $v\in L^2$, and $g$ a complex Schwartz function on $(\text{mixed space of }L)^2$. Let $\iota$ be a finite type and $b:\iota\to M_2(L)$ a $K$-linearly independent family whose $K$-span is exactly $\{X : X\delta_0=\delta_0\,X^\sigma\}$ (entrywise $\sigma$). Equip $K_\infty=\mathrm{InfiniteAdeleRing}\,K$ with a Borel $\sigma$-algebra for its topology, give $K_\infty$ and $E=L\otimes_KK_\infty$ the real algebra structures transported through the isomorphism with the mixed space of $K$, and $M_2(E)$ its Borel $\sigma$-algebra. Then there is an additive Haar measure $\nu$ on $K_\infty^\iota$ giving mass $1$ to the set of $a$ with every $a_k$ in the preimage of the fundamental domain of $\mathrm{mixedEmbedding.latticeBasis}\,K$, such that for all $n_2$ and every $\mathbb{R}$-linearly independent $e_2:\mathrm{Fin}\,n_2\to M_2(E)$ whose $\mathbb{R}$-span is $\{X : X\delta=\delta\,X^{\sigma\otimes\mathrm{id}}\}$, with $\delta$ the archimedean component (image under $\mathrm{tensorArch}$, i.e. $\mathrm{id}_L\otimes$ the adelic-to-archimedean map) of $(\delta_0\otimes 1)\cdot c I_2$, one has $$\sqrt{\bigl|\det\bigl(\mathrm{Tr}_{E/\mathbb{R}}\,\mathrm{tr}(e_{2,i}e_{2,j})\bigr)\bigr|}\int_{\mathbb{R}^{n_2}}\Re\,g\bigl(\textstyle\sum_k c_ke_{2,k}\cdot(v\otimes1)\bigr)dc=\sqrt{|d_K|^{\#\iota}\bigl|N_{K/\mathbb{Q}}\det(\mathrm{Tr}_{L/K}\,\mathrm{tr}(b_ib_j))\bigr|}\int_{K_\infty^\iota}\Re\,g\bigl(\textstyle\sum_k b_k\otimes a_k\cdot(v\otimes1)\bigr)d\nu,$$ the matrix acting on the column $(v_j\otimes 1)_j$ and the resulting vector read in the mixed space of $L$ via $\mathrm{archIdent}$ and the mixed-space isomorphism; both integrals are lower Lebesgue integrals of $\mathrm{ofReal}$ of the real parts.
--
--   This is the archimedean covolume comparison underlying the twisted orbital integral computation: it replaces the Lebesgue integral over the real span of the archimedean twisted commutant of $\delta$, normalised by the Gram determinant of the trace form, by an integral over $K_\infty^\iota$ against the Haar measure normalised by the fundamental parallelepiped of an integral basis of $K$, at the cost of the covolume constant $\sqrt{|d_K|^{\#\iota}|N_{K/\mathbb{Q}}\det G_b|}$. It feeds the global form of the identity, where the archimedean factor is combined with the measure of an adelic box at the finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal SchwartzMap Classical

theorem AutomorphicForm.exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (v : Fin 2 → L) (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ ν : Measure (ι → InfiniteAdeleRing K), ν.IsAddHaarMeasure ∧
      ν {a : ι → InfiniteAdeleRing K | ∀ k, a k ∈ infiniteBox K} = 1 ∧
      ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
            Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
          ∫⁻ cc : Fin n₂ → ℝ, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, cc k • e₂ k).mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) =
        (ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ∫⁻ a : ι → InfiniteAdeleRing K, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).mulVec
              fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re ∂ν) := by sorry
