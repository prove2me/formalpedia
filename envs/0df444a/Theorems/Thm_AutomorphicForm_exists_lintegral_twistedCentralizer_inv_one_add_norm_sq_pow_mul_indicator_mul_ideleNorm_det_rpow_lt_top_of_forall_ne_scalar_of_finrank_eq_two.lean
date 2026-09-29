-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/600ff576-c926-51f3-a467-01730988ed92
-- title:
--   Convergence of the twisted-centralizer zeta integral for s₁>1
-- statement:
--   Fix number fields $K$ and $L$ with $L$ a $K$-algebra such that $\operatorname{finrank}_K L = 2$ (hypothesis `h2`), and an automorphism $\sigma \in \mathrm{Aut}_K(L)$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$ (hypothesis `hgen`). Fix further $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ and a unit $u$ of $\mathbb{A}_K$, where $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`. Throughout, $\delta$ denotes the element $\delta_0 \cdot c$ of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, that is, the product of the image of $\delta_0$ under the entrywise map induced by `Algebra.TensorProduct.includeLeftRingHom` and the scalar matrix attached to $c$.
--
--   For a commutative $K$-algebra $A$, [`AutomorphicForm.sigmaTensor K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L199) is the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K A$, [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) is its entrywise extension to $\mathrm{GL}_2(L \otimes_K A)$, [`AutomorphicForm.normString K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L205) sends $\gamma$ to $\prod_{i < \operatorname{finrank}_K L} (\sigma_{\mathrm{GL}})^{i}(\gamma)$, and [`AutomorphicForm.twistedCentralizer K L A σ γ`](def/AutomorphicForm_TwistedOrbital.html#L220) is the subgroup $\{t : t\,\gamma\,\sigma_{\mathrm{GL}}(t)^{-1} = \gamma\}$ of $\mathrm{GL}_2(L \otimes_K A)$. Also [`AutomorphicForm.toTensorGL K L A`](def/AutomorphicForm_TwistedOrbital.html#L71) is the entrywise map $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by `Algebra.TensorProduct.includeRight`, and [`AutomorphicForm.tensorArch K L`](def/AutomorphicForm_BaseChangePlaces.html#L46), [`AutomorphicForm.tensorPlace K L v`](def/AutomorphicForm_BaseChangePlaces.html#L49) are the entrywise maps $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K) \to \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $\to \mathrm{GL}_2(L \otimes_K K_v)$ induced by the projections of $\mathbb{A}_K$ to the infinite adeles and to the completion at a finite place $v$. All groups and subgroups of matrix groups occurring carry their Borel structures.
--
--   The hypotheses on $\delta$ are: `hN`, that the norm string of $\delta$, i.e. $\delta \cdot \sigma_{\mathrm{GL}}(\delta)$, equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of the scalar matrix $\mathrm{diag}(u,u)$ in $\mathrm{GL}_2(\mathbb{A}_K)$; and `hns`, that for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ is $x^{-1} \delta_0 \, \sigma(x)$ the scalar matrix $\mathrm{diag}(z,z)$, where $\sigma$ acts entrywise.
--
--   The measures are: a Haar measure $\tau_a'$ on the $\sigma$-twisted centralizer of `tensorArch` $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ (hypothesis `hτa'`), a family of Haar measures $\tau_f'(v)$ on the $\sigma$-twisted centralizers of `tensorPlace` $v$ $\delta$ in $\mathrm{GL}_2(L \otimes_K K_v)$, $v$ running over the finite places of $K$ (hypothesis `hτf'`), and a Haar measure $\tau'$ on the $\sigma$-twisted centralizer $T'$ of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ (hypothesis `hτ'`).
--
--   A constant $s \in [0,\infty]$ is given together with hypothesis `harch`: with respect to the $\mathbb{R}$-algebra structures on $\mathbb{A}_{K,\infty}$ (through `InfiniteAdeleRing.ringEquiv_mixedSpace` and the mixed space) and on $L \otimes_K \mathbb{A}_{K,\infty}$ (through `Algebra.TensorProduct.includeRight`), there exist $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly the set of matrices $X$ with $X \cdot \delta_\infty = \delta_\infty \cdot (\sigma \otimes \mathrm{id})(X)$ (entrywise application of `sigmaTensor`), where $\delta_\infty =$ `tensorArch` $\delta$, and such that the pushforward of $\tau_a'$ along the inclusion of the twisted centralizer into $M_2(L \otimes_K \mathbb{A}_{K,\infty})$ equals $s$ times the measure obtained as follows: the pushforward of Lebesgue measure on $\mathbb{R}^{n_2}$ along $c \mapsto \sum_i c_i e_2(i)$, scaled by $\sqrt{|\det(\operatorname{tr}_{\mathbb{R}} \operatorname{tr}(e_2(i) e_2(j)))_{i,j}|}$, then given the density $X \mapsto |N_{\mathbb{R}}(\det X)|^{-1}$ (as extended non-negative reals).
--
--   Local data at the finite places: a family of constants $t_v \in [0,\infty]$ and a finite set $S_0$ of finite places of $K$ with $t_v = 1$ for $v \notin S_0$ (hypothesis `ht`), subject to hypothesis `hfin`, which requires for every finite place $v$ one of two alternatives. Either there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator, in the sense that the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of the $v$-component of the finite part of the scalar matrix $\mathrm{diag}(u,u)$ equals $y^{-1} \cdot (\text{norm string of } \delta_v) \cdot y$, and the pushforward of $\tau_f'(v)$ along $t \mapsto y^{-1} t y$ equals $t_v$ times the pushforward of the local Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ (normalised so that the integral units set has mass one) along [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71). Or else both: no scalar matrix $\mathrm{diag}(z,z)$, $z$ a unit of $L \otimes_K K_v$, is $\sigma$-conjugate to $\delta_v$ (there is no $x$ with $\mathrm{diag}(z,z) = x^{-1} \delta_v \sigma_{\mathrm{GL}}(x)$); and, writing $E_v$ for the set of $t$ in the local twisted centralizer whose determinant is the image under `Algebra.TensorProduct.includeRight` of a unit $s$ of $K_v$ with $|s|_v = 1$, one has $\tau_f'(v)(E_v) \cdot \mathrm{N}(v) = t_v + \tau_f'(v)(E_v)$, with $\mathrm{N}(v)$ the absolute norm of the prime ideal of $v$.
--
--   Finally, a constant $c_{\tau'}$ with $c_{\tau'} > 0$ (hypothesis `hcτ'`) is given together with the product-formula hypothesis `hτ'prod`: for every finite set $S$ of finite places with $S_0 \subseteq S$ and all functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $W_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$, all complex valued, such that $W_a$ is almost everywhere strongly measurable on the archimedean twisted centralizer for $\tau_a'$, each $W_S(v)$ for $v \in S$ is almost everywhere strongly measurable for $\tau_f'(v)$, $W(t) = W_a(\text{tensorArch } t)\prod_{v \in S} W_S(v)(\text{tensorPlace } v\ t)$ whenever the local components of $t$ at all $v \notin S$ lie in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (the set of $g$ such that $g$ and $g^{-1}$ have entries in the image of the semilocal integers of $L$ at $v$), and $W(t) = 0$ whenever some component at a place outside $S$ fails to lie in that set, the identity $\int_{T'} W \, d\tau' = c_{\tau'} \left(\int W_a \, d\tau_a'\right) \prod_{v \in S} \int W_S(v) \, d\tau_f'(v)$ holds.
--
--   Let moreover $\mathbf{v} : \mathrm{Fin}\,2 \to L$ be nonzero (hypothesis `hv`) and $s_1$ a real number with $s_1 > 1$ (hypothesis `hs₁`).
--
--   The conclusion asserts the existence of a natural number $M$ such that the lower Lebesgue integral over $T'$ with respect to $\tau'$ of the product of the following three factors is finite (strictly less than $\top$). Write $E$ for the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ given by `Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), applied entrywise to $t \in T'$ to give a matrix $E(t) \in M_2(\mathbb{A}_L)$, and let $\mathrm{col}(t) = E(t) \cdot (\text{image of } \mathbf{v} \text{ in } \mathbb{A}_L^2)$ be the corresponding matrix-vector product. The first factor is $\mathrm{ofReal}\big((1 + \|(\mathrm{col}(t)_i)_\infty\|^2)^{-M}\big)$, where the archimedean component of each coordinate of $\mathrm{col}(t)$ is read in the mixed space of $L$ through `InfiniteAdeleRing.ringEquiv_mixedSpace L` and the norm is that of the resulting function on $\mathrm{Fin}\,2$. The second factor is the indicator function, with value $1$ in $[0,\infty]$, of the set of those $t$ for which the finite component of every coordinate of $\mathrm{col}(t)$ lies in `integralFiniteAdeles (𝓞 L) L`, i.e. is integral at every finite place of $L$. The third factor is $\mathrm{ofReal}\big(\|\det E(t)\|^{s_1}\big)$, where $\|\cdot\|$ is the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), the value at the argument of the distributive Haar character of $\mathbb{A}_L$, raised to the real power $s_1$.
--
--   This is the convergence statement for the zeta integral of the $\sigma$-twisted centralizer $T'$ — the adelic unit group of the quaternion algebra attached to $\delta$ — against the standard majorant built from a sup-norm bound at the archimedean places, integrality of the image vector at the finite places, and the $s_1$-th power of the idele norm of the determinant; under the assumed factorisation of $\tau'$ into $\tau_a'$ and the $\tau_f'(v)$, finiteness for $s_1 > 1$ reflects the convergence of $\zeta_K(2s_1)\zeta_K(2s_1-1)$. It is used in the treatment of zeta integrals against Schwartz–Bruhat functions, in [`AutomorphicForm.lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two.lean

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

open MeasureTheory Filter NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open NumberField

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.exists_lintegral_twistedCentralizer_inv_one_add_norm_sq_pow_mul_indicator_mul_ideleNorm_det_rpow_lt_top_of_forall_ne_scalar_of_finrank_eq_two
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
    (s₁ : ℝ) (hs₁ : 1 < s₁) :
    ∃ M : ℕ,
      ∫⁻ t, ENNReal.ofReal (((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1‖ ^ 2) ^ M)⁻¹) *
          Set.indicator {t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c)) |
              ∀ i, ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2 ∈ integralFiniteAdeles (𝓞 L) L}
            (fun _ => (1 : ℝ≥0∞)) t *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤ := by sorry
