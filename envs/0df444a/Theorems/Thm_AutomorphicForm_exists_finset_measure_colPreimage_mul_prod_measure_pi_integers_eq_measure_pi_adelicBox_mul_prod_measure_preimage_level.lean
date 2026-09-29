-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level
-- name    : AutomorphicForm.exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/559beefb-3ffa-5760-a31c-96ae40555b5f
-- title:
--   Column-preimage mass equals adelic box mass times local masses
-- statement:
--   Let $K \subset L$ be number fields with $[L:K]=2$, let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism lies in $\langle \sigma\rangle$, let $\delta_0 \in \mathrm{GL}_2(L)$, $c \in (L\otimes_K \mathbb{A}_K)^\times$, $u \in \mathbb{A}_K^\times$, and write $\delta$ for the image of $\delta_0$ in $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ times the scalar matrix $c$. Assume the norm string of $\delta$, the product of the iterates $(\sigma\text{-twist})^i\delta$ for $i<[L:K]$, equals the image of the scalar matrix $u$ under $\mathrm{GL}_2(\mathbb{A}_K)\to\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$, and that $x^{-1}\delta_0\,\sigma(x)$ is never a scalar matrix for $x\in\mathrm{GL}_2(L)$. Let $v\in L^2$ be nonzero, $U\subseteq (\mathbb{A}_{L,f})^2$ open and compact, $S_1$ a finite set of finite places of $K$, and $W_w\subseteq \mathrm{GL}_2(L\otimes_K K_w)$ Borel sets such that: for $w\notin S_1$, an element of the twisted centraliser $\{t\mid t\,\delta_w\,\sigma(t)^{-1}=\delta_w\}$ of the local component $\delta_w$ lies in $W_w$ exactly when all its entries lie in the image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_w}$; and for every finite $S\supseteq S_1$ and every $t$ in the twisted centraliser of $\delta$ over $\mathbb{A}_K$ whose components at $w\notin S$ and their inverses have semi-local integral entries, $\mathbf 1_U$ of the finite part of $t\cdot v$, computed through the ring isomorphism $\mathbb{A}_K\otimes_K L\cong \mathbb{A}_L$, equals $\prod_{w\in S}\mathbf 1_{W_w}(t_w)$. Let $b:\iota\to M_2(L)$, with $\iota$ of cardinality $4$, be $K$-linearly independent with span exactly $\{X \mid X\delta_0 = \delta_0 X^\sigma\}$, let $\rho$ be an additive Haar measure on $\mathbb{A}_K^\iota$ and $\mu_w$ additive Haar measures on $K_w^\iota$. Then there is a finite set $S_2 \supseteq S_1$ of finite places of $K$ such that for every finite $S \supseteq S_2$, $$\rho\{a\mid a_{k,\infty}\in\mathcal{P}\ \forall k,\ (\textstyle\sum_k b_k\otimes a_k)\cdot v \text{ has finite part in } U\}\cdot\prod_{w\in S}\mu_w\bigl((\mathcal{O}_{K_w})^\iota\bigr) = \rho\bigl((\mathcal{P}\times\widehat{\mathcal{O}}_K)^\iota\bigr)\cdot\prod_{w\in S}\mu_w\{a\mid \exists t\in W_w \text{ in the twisted centraliser of }\delta_w,\ t=\textstyle\sum_k b_k\otimes a_k\},$$ where $\mathcal{P}$ is the fundamental domain of the lattice $\mathcal{O}_K$ in $K\otimes\mathbb{R}$ pulled back to the infinite adeles and $\mathcal{P}\times\widehat{\mathcal{O}}_K$ is the corresponding adelic box.
--
--   This is the finite-place bookkeeping step in the covolume computation for the twisted centraliser of $\delta_0$: it converts the mass of the preimage of the level set $U$ under the column map into the mass of the standard adelic box corrected by purely local volumes at the places of $S$. It is used in the covolume identity [`AutomorphicForm.prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq`](thm.html#AutomorphicForm.prod_corr_one_mul_sqrt_discr_pow_mul_norm_det_mul_measure_pi_adelicBox_eq_measure_colPreimage_mul_two_pow_mul_prod_mul_discr_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level.lean

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

theorem AutomorphicForm.exists_finset_measure_colPreimage_mul_prod_measure_pi_integers_eq_measure_pi_adelicBox_mul_prod_measure_preimage_level
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
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))

    (ι : Type) [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 K), MeasurableSpace (w.adicCompletion K)]
    [∀ w : HeightOneSpectrum (𝓞 K), BorelSpace (w.adicCompletion K)]
    (μ : ∀ w : HeightOneSpectrum (𝓞 K), Measure (ι → w.adicCompletion K)) [∀ w, (μ w).IsAddHaarMeasure] :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S₂ ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₂ ⊆ S →
      ρ {a : ι → AdeleRing (𝓞 K) K | (∀ k, (a k).1 ∈ infiniteBox K) ∧
          (fun i => ((((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
            fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) i).2) ∈ U} *
          ∏ v ∈ S, μ v {a : ι → v.adicCompletion K | ∀ k, a k ∈ v.adicCompletionIntegers K} =
        ρ {a : ι → AdeleRing (𝓞 K) K | ∀ k, a k ∈ adelicBox K} *
          ∏ v ∈ S, μ v {a : ι → v.adicCompletion K | ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)} := by sorry
