-- Prove2me | Theorems.Thm_AutomorphicForm_sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_measure_colPreimage_eq_lintegral_pairHaar_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox
-- name    : AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_measure_colPreimage_eq_lintegral_pairHaar_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6ab18c0b-d38c-5744-8986-bafbf088ee05
-- title:
--   Adelic covolume identity for the twisted-commutant column map
-- statement:
--   Let $K \subset L$ be number fields with $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-automorphism of $L$ is an integer power of $\sigma$, let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbb{A}_K$ and $u$ a unit of $\mathbb{A}_K$, and put $\delta = \delta_0 \cdot \operatorname{scalar}(c) \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ (the image of $\delta_0$ under $l \mapsto l \otimes 1$ times the scalar matrix of $c$). Assume the norm string $\prod_{i<2} \sigma_{\mathrm{GL}}^{i}(\delta)$, where $\sigma_{\mathrm{GL}}$ is induced by $\sigma \otimes \mathrm{id}$, equals the scalar matrix of $1 \otimes u$, and that $x^{-1} \delta_0\, \sigma(x)$ is never a scalar matrix $\operatorname{scalar}(z)$ for $x \in \mathrm{GL}_2(L)$, $z \in L^{\times}$. Let $v \in L^2$ be nonzero, $\mu_1$ an additive Haar measure on $\mathbb{A}_L$ with $\mu_1$ of the adelic box (fundamental domain of the lattice basis at the infinite places times the integral finite adeles) equal to $1$, $U \subset (\mathbb{A}_{L,f})^2$ open and compact, $g$ a Schwartz function on $(\mathbb{R}^{r_1} \times \mathbb{C}^{r_2})^2$ valued in $\mathbb{C}$ with compact support and with $g(y)$ real and non-negative for all $y$. Let $\iota$ be a finite type of cardinality $4$ and $b : \iota \to M_2(L)$ a $K$-linearly independent family whose $K$-span is exactly $\{X : X\delta_0 = \delta_0 X^{\sigma}\}$, and let $\rho$ be an additive Haar measure on $\iota \to \mathbb{A}_K$; measurable- and Borel-space instances are as usual. Equip $\mathbb{A}_{K,\infty}$ and $L \otimes_K \mathbb{A}_{K,\infty}$ with the real algebra structures coming from the isomorphism of $\mathbb{A}_{K,\infty}$ with the mixed space, and $M_2(L \otimes_K \mathbb{A}_{K,\infty})$ with its Borel structure. The assertion is that for every $n_2$ and every $\mathbb{R}$-linearly independent $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly $\{X : X \delta_\infty = \delta_\infty X^{\sigma \otimes \mathrm{id}}\}$, with $\delta_\infty$ the image of $\delta$ under $\mathrm{id}_L \otimes (\mathbb{A}_K \to \mathbb{A}_{K,\infty})$, one has $$\sqrt{|\det(\operatorname{Tr}_{\mathbb{R}}\operatorname{tr}(e_{2,i}e_{2,j}))|} \cdot \int_{\mathbb{R}^{n_2}} g\bigl((\textstyle\sum_k c_k e_{2,k})\cdot (v \otimes 1)\bigr)\,dc \cdot \rho\{a : a_k \text{ infinite part in the box for all } k,\ \text{finite part of } (\textstyle\sum_k b_k \otimes a_k)v \in U\}$$ equals $$\Bigl(\int_{(\mathbb{A}_L)^2} g(x_\infty)\,\mathbf{1}_U(x_f)\,d(\mu_1 \times \mu_1)\Bigr) \cdot \sqrt{|d_K|^{\#\iota}\,\bigl|N_{K/\mathbb{Q}} \det(\operatorname{Tr}_{L/K}\operatorname{tr}(b_i b_j))\bigr|} \cdot \rho\{a : a_k \in \text{adelic box of } K \text{ for all } k\},$$ all integrals being lower Lebesgue integrals of the real parts, the column map being read through $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ and, archimedeanly, through $L \otimes_K \mathbb{A}_{K,\infty} \cong \mathbb{A}_{L,\infty}$ followed by the identification with the mixed space.
--
--   This is the covolume identity comparing the archimedean Gram-determinant normalisation of the twisted commutant $\{X : X\delta_0 = \delta_0 X^\sigma\}$ with the box-normalised Haar measure on $(\mathbb{A}_L)^2$, in the shape in which it is applied to Godement sections attached to a twisted orbital integral. It feeds the final form of the identity, in which the right-hand constant is evaluated as a power of $2$ times a discriminant square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_measure_colPreimage_eq_lintegral_pairHaar_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.sqrt_det_gram_mul_lintegral_schwartzMap_archIdent_mul_measure_colPreimage_eq_lintegral_pairHaar_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U)
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)) (hg : HasCompactSupport g)
    (hg' : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0)

    (ι : Type) [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
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
            (AutomorphicForm.archIdent K L (((∑ k, cc k • e₂ k).mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) *
          ρ {a : ι → AdeleRing (𝓞 K) K | (∀ k, (a k).1 ∈ infiniteBox K) ∧
          (fun i => ((((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
            fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) i).2) ∈ U} =
      (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
        (ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K}) := by sorry
