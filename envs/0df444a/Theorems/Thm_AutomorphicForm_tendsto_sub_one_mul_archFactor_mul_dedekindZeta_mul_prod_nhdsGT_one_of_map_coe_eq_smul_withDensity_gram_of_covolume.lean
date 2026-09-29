-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
-- name    : AutomorphicForm.tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/58b1eb1c-be13-5c08-8a9b-74a06ab0fa6a
-- title:
--   Residue at s'=1 of a twisted adelic zeta integral
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an algebra over $K$ such that $\operatorname{finrank}_K L = 2$, and $\sigma : L \simeq_K L$ is a $K$-automorphism of $L$ with the property (`hgen`) that every $K$-automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Further data are an element $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c \in (L \otimes_K \mathbb{A}_K)^\times$ and a unit $u \in \mathbb{A}_K^\times$, where $\mathbb{A}_K$ denotes the adele ring of $K$ over $\mathcal{O}_K$. Write $\delta$ for the element of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ obtained as the product of the entrywise image of $\delta_0$ under $L \to L \otimes_K \mathbb{A}_K$ with the scalar matrix $c \cdot I$, and write $\sigma_{\mathrm{GL}}$ for the entrywise action of $\sigma \otimes \mathrm{id}$ on $\mathrm{GL}_2(L \otimes_K A)$ for any $K$-algebra $A$.
--
--   Two conditions tie $\delta$ to $u$ and exclude the scalar case. The hypothesis `hN` states that the norm string of $\delta$, namely the product $\prod_{i=0}^{\operatorname{finrank}_K L - 1} \sigma_{\mathrm{GL}}^{i}(\delta)$, equals the entrywise image under $\mathbb{A}_K \to L \otimes_K \mathbb{A}_K$ of the scalar matrix $u \cdot I$. The hypothesis `hns` states that for every $x \in \mathrm{GL}_2(L)$ and every $z \in L^\times$ one has $x^{-1} \delta_0 \, \sigma(x) \neq z \cdot I$, where $\sigma(x)$ is the entrywise image of $x$ under $\sigma$.
--
--   For a $K$-algebra $A$ the $\sigma$-twisted centraliser of an element $\eta \in \mathrm{GL}_2(L \otimes_K A)$ is the subgroup $\{t : t\,\eta\,\sigma_{\mathrm{GL}}(t)^{-1} = \eta\}$. Measures are given on the twisted centralisers of the local components of $\delta$: a Haar measure $\tau_\infty'$ (hypothesis `hτa'`) on the twisted centraliser of $\delta_\infty$, the image of $\delta$ in $\mathrm{GL}_2(L \otimes_K K_\infty)$ under base change to the infinite adele ring, and for each finite place $v$ of $K$ a Haar measure $\tau_v'$ (hypothesis `hτf'`) on the twisted centraliser of $\delta_v$, the image of $\delta$ in $\mathrm{GL}_2(L \otimes_K K_v)$; all these groups and the matrix algebras carry their Borel structures. A constant $s \in [0,\infty]$ with $s \neq \infty$ (`hs`) is fixed.
--
--   The archimedean normalisation `harch` is stated for the $\mathbb{R}$-algebra structures on $K_\infty$ coming from the identification with the mixed space of $K$ and on $L \otimes_K K_\infty$ coming from the right inclusion, and asserts the existence of $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K K_\infty)$ whose $\mathbb{R}$-span is exactly the set of matrices $X$ with $X \delta_\infty = \delta_\infty \, X^{\sigma}$ ($X^\sigma$ the entrywise image of $X$ under $\sigma \otimes \mathrm{id}$), such that the push-forward of $\tau_\infty'$ under the inclusion of the twisted centraliser into $M_2(L \otimes_K K_\infty)$ equals
--   $$s \cdot \Bigl( \sqrt{\bigl|\det\bigl(\operatorname{tr}_{\mathbb{R}}^{L \otimes_K K_\infty}\operatorname{tr}(e_2(i) e_2(j))\bigr)_{i,j}\bigr|} \cdot \lambda_{e_2} \Bigr) \text{ with density } X \mapsto |N_{\mathbb{R}}(\det X)|^{-1},$$
--   where $\lambda_{e_2}$ is the push-forward of Lebesgue measure on $\mathbb{R}^{n_2}$ under $c \mapsto \sum_i c_i e_2(i)$ and $N_{\mathbb{R}}$ is the algebra norm of $L \otimes_K K_\infty$ over $\mathbb{R}$.
--
--   The local normalisations are governed by a function $t$ from the finite places of $K$ to $[0,\infty]$, a finite set $S_0$ of finite places with $t_v = 1$ for $v \notin S_0$ (`ht`), and the hypothesis `hfin`, which requires for each finite place $v$ one of two alternatives. Either there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ such that the entrywise image of the scalar matrix $u_v \cdot I \in \mathrm{GL}_2(K_v)$ (the component at $v$ of the finite part of $u \cdot I$) under $K_v \to L \otimes_K K_v$ equals $y^{-1} \cdot \bigl(\prod_{i=0}^{\operatorname{finrank}_K L - 1}\sigma_{\mathrm{GL}}^i(\delta_v)\bigr) \cdot y$, and the push-forward of $\tau_v'$ under $t \mapsto y^{-1} t y$ equals $t_v$ times the push-forward under $K_v \to L \otimes_K K_v$ of the Haar measure on $\mathrm{GL}_2(K_v)$ normalised to give mass $1$ to the compact open set of matrices having entries, and inverse entries, in the valuation ring; or else $\delta_v$ is not $\sigma$-conjugate to any central scalar, that is, for every $z \in (L \otimes_K K_v)^\times$ there is no $x$ with $z \cdot I = x^{-1}\delta_v \sigma_{\mathrm{GL}}(x)$, and, writing $E_v$ for the set of $t$ in the twisted centraliser whose determinant is the image under $K_v \to L \otimes_K K_v$ of some $s \in K_v^\times$ with $|s|_v = 1$, one has $\tau_v'(E_v) \cdot \mathrm{N}(v) = t_v + \tau_v'(E_v)$, with $\mathrm{N}(v)$ the absolute norm of the prime ideal of $v$.
--
--   Globally, $\tau'$ is a Haar measure (`hτ'`) on the twisted centraliser of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, and $c_{\tau'}$ is a real number with $c_{\tau'} > 0$ (`hcτ'`). The hypothesis `hτ'prod` is a factorisation property of $\tau'$: for every finite set $S$ of finite places with $S_0 \subseteq S$ and all complex-valued functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_\infty$ on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $W_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$, if $W_\infty$ is almost everywhere strongly measurable for $\tau_\infty'$ on the archimedean twisted centraliser, each $W_v$ for $v \in S$ is almost everywhere strongly measurable for $\tau_v'$, if $W(t) = W_\infty(t_\infty) \prod_{v \in S} W_v(t_v)$ for every $t$ in the adelic twisted centraliser all of whose components $t_v$ with $v \notin S$ lie in the set of elements of $\mathrm{GL}_2(L \otimes_K K_v)$ having entries, and inverse entries, in the semi-local integers (the range of the canonical map of the semi-local integral closure into $L \otimes_K K_v$), and if $W(t) = 0$ whenever some component $t_v$ with $v \notin S$ fails to lie in that set, then
--   $$\int W \, d\tau' = c_{\tau'} \Bigl(\int W_\infty \, d\tau_\infty'\Bigr) \prod_{v \in S} \int W_v \, d\tau_v'.$$
--
--   The remaining data are a nonzero vector $v \in L^2$, a measurable and Borel structure on the adele ring $\mathbb{A}_L$ of $L$ together with an additive Haar measure $\mu_1$ on $\mathbb{A}_L$ normalised by $\mu_1(\mathrm{adelicBox}\,L) = 1$ (the product of the preimage of a fundamental domain for the lattice of $\mathcal{O}_L$ in the mixed space with the set of integral finite adeles); a set $U \subseteq (\mathrm{Fin}\,2 \to \mathbb{A}_{L,\mathrm{fin}})$; a Schwartz function $g$ on $\mathrm{Fin}\,2 \to$ (mixed space of $L$) with values in $\mathbb{C}$; a finite set $S_1$ of finite places of $K$; a function $G : M_2(L \otimes_K K_\infty) \to [0,\infty]$ which is Borel measurable (`hGm`), bounded by a constant $C \neq \infty$ (`hC`, `hGC`) and vanishing off a compact set $S$ (`hS`, `hGS`); and correction factors $\mathrm{Corr}_v : \mathbb{R} \to [0,\infty]$ such that for $v \in S_1$ the function $\mathrm{Corr}_v$ tends to $\mathrm{Corr}_v(1)$ along the filter of right neighbourhoods of $1$ and $\mathrm{Corr}_v(1) \neq \infty$ (`hCorr`).
--
--   Under these hypotheses the conclusion asserts, for the same $\mathbb{R}$-algebra and Borel structures as in `harch`: for every $n_2 \in \mathbb{N}$ and every $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K K_\infty)$ such that the push-forward of $\tau_\infty'$ to $M_2(L \otimes_K K_\infty)$ equals $s$ times the Gram-scaled measure $\sqrt{|\det(\operatorname{tr}_{\mathbb{R}}\operatorname{tr}(e_2(i)e_2(j)))_{i,j}|} \cdot \lambda_{e_2}$ with density $X \mapsto |N_{\mathbb{R}}(\det X)|^{-1}$, and such that the covolume identity
--   $$\Bigl( \sqrt{\bigl|\det(\operatorname{tr}_{\mathbb{R}}\operatorname{tr}(e_2(i)e_2(j)))_{i,j}\bigr|} \cdot \int^{-}_{\mathbb{R}^{n_2}} G\Bigl(\sum_i c_i e_2(i)\Bigr)\,dc \Bigr) \cdot \prod_{v \in S_1} \mathrm{Corr}_v(1) = \Phi \cdot 2^{2\,[K:\mathbb{Q}]} \cdot \Bigl(\prod_{v \in S_0} t_v\Bigr) \cdot (d_K)^2$$
--   holds, where $[K:\mathbb{Q}] = \operatorname{finrank}_{\mathbb{Q}} K$, $d_K$ is the discriminant of $K$ viewed as a real number, and
--   $$\Phi = \int^{-}_{(\mathrm{Fin}\,2 \to \mathbb{A}_L)} \operatorname{ofReal}\Bigl(\operatorname{Re}\bigl( g\bigl(i \mapsto \rho_L(x_i)_\infty\bigr)\cdot \mathbf{1}_U\bigl(i \mapsto (x_i)_{\mathrm{fin}}\bigr)\bigr)\Bigr)\, d(\mu_1 \otimes \mu_1),$$
--   with $\rho_L$ the identification of the infinite adeles of $L$ with the mixed space and $\mathbf{1}_U$ the indicator of $U$ with value $1$; then, as $s' \to 1^{+}$ (along the filter of right neighbourhoods of $1$ in $\mathbb{R}$),
--   $$\operatorname{ofReal}(s'-1)\cdot\Bigl( \operatorname{ofReal}(c_{\tau'}) \cdot \Bigl( \int^{-} G(t)\cdot \operatorname{ofReal}\bigl(|N_{\mathbb{R}}(\det t)|^{s'}\bigr)\, d\tau_\infty' \Bigr) \cdot \Bigl( \operatorname{ofReal}\bigl(\operatorname{Re}(\zeta_K(2s')\,\zeta_K(2s'-1))\bigr) \cdot \prod_{v \in S_1} \mathrm{Corr}_v(s') \Bigr)\Bigr)$$
--   converges, in $[0,\infty]$, to
--   $$2^{-1} \cdot \Phi \cdot \Bigl( \operatorname{ofReal}(c_{\tau'}) \cdot s \cdot 2^{2\,[K:\mathbb{Q}]} \cdot \Bigl(\prod_{v \in S_0} t_v\Bigr) \cdot \operatorname{ofReal}\bigl( (d_K)^2 \cdot \operatorname{Re}(\zeta_K(2)) \cdot \operatorname{res}_{s=1}\zeta_K \bigr) \Bigr),$$
--   where the integral over $\tau_\infty'$ is taken over the archimedean twisted centraliser with $t$ read as a matrix, $\zeta_K$ is the Dedekind zeta function of $K$ and $\operatorname{res}_{s=1}\zeta_K$ its residue at $s = 1$.
--
--   This is the residue-extraction step for the zeta integral attached to the $\sigma$-twisted centraliser of $\delta$: the pole at $s'=1$ of $\zeta_K(2s')\zeta_K(2s'-1)$ is cancelled against the factor $s'-1$, and the resulting constant is expressed through the archimedean covolume, the local normalisations $t_v$ and the discriminant of $K$, in the shape of a mass formula. It feeds the limit statement [`AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol`](thm.html#AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol), and uses the analytic input [`NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT`](thm.html#NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT) together with the archimedean finiteness and convergence result [`AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram`](thm.html#AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume.lean

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
open scoped Classical in

theorem AutomorphicForm.tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
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

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)

    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G) (C : ℝ≥0∞) (hC : C ≠ ⊤) (hGC : ∀ X, G X ≤ C)
    (S : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) (hS : IsCompact S) (hGS : ∀ X ∉ S, G X = 0)
    (hs : s ≠ ⊤)
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)) ∧ Corr v 1 ≠ ⊤) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) →

      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) * ∏ v ∈ S₁, Corr v 1 =
        (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
          ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2) →
      Tendsto (fun s' : ℝ => ENNReal.ofReal (s' - 1) *
          (ENNReal.ofReal cτ' * (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))), G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
              ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s') ∂τa') *
            (ENNReal.ofReal ((NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) *
                NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re) * ∏ v ∈ S₁, Corr v s')))
        (𝓝[>] (1 : ℝ))
        (𝓝 (2⁻¹ * ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))))) := by sorry
