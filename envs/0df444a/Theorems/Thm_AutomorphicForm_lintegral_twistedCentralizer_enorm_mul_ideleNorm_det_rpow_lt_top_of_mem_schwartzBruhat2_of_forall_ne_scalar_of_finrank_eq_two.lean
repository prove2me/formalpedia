-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/765307b2-390f-53ba-8cc5-e97a73bdd4f8
-- title:
--   Absolute convergence of the twisted-centralizer zeta integral for s₁>1
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ of degree $2$ (hypothesis `h2`: $\operatorname{finrank}_K L = 2$), and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integral powers of $\sigma$ (hypothesis `hgen`). Let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbb{A}_K$ (the adele ring of $K$ being written $\mathbb{A}_K$), and let $u$ be an idele class representative, i.e. a unit of $\mathbb{A}_K$. Throughout, $\delta$ denotes the element $(\delta_0 \otimes 1)\cdot \mathrm{scalar}(c)$ of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, obtained by applying `Matrix.GeneralLinearGroup.map` to $\delta_0$ along the ring homomorphism $L \to L \otimes_K \mathbb{A}_K$, $x \mapsto x \otimes 1$, and multiplying by the scalar matrix with entry $c$. For a commutative $K$-algebra $A$, [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) denotes the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced entrywise by $\sigma \otimes \mathrm{id}_A$, [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205) denotes the product $\delta \cdot \sigma(\delta) \cdots \sigma^{[\,n-1]}(\delta)$ with $n = \operatorname{finrank}_K L$ factors, and the twisted centralizer [`AutomorphicForm.twistedCentralizer K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L220) is the subgroup $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\mathrm{GL}_2(L \otimes_K A)$. The archimedean and $v$-adic components of $\delta$, namely its images under the maps [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46) into $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and [`AutomorphicForm.tensorPlace`](def/AutomorphicForm_BaseChangePlaces.html#L49) at a finite place $v$ into $\mathrm{GL}_2(L \otimes_K K_v)$, are written $\delta_\infty$ and $\delta_v$.
--
--   Two hypotheses fix the conjugacy type of $\delta$: hypothesis `hN` asserts that the norm string of $\delta$ equals the image of the central scalar matrix with entry $u$ under $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ induced by $a \mapsto 1 \otimes a$; hypothesis `hns` asserts that for every $x \in \mathrm{GL}_2(L)$ and every $z \in L^\times$ one has $x^{-1}\delta_0\,\sigma(x) \neq \mathrm{scalar}(z)$, i.e. $\delta_0$ is not $\sigma$-conjugate over $L$ to a scalar matrix.
--
--   Measures are given as follows. Let $\tau_\infty'$ be a Haar measure (hypothesis `hτa'`) on the twisted centralizer of $\delta_\infty$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, and for each finite place $v$ of $K$ let $\tau_v'$ be a Haar measure (hypothesis `hτf'`) on the twisted centralizer of $\delta_v$ in $\mathrm{GL}_2(L \otimes_K K_v)$. Let $s \in [0,\infty]$. The archimedean normalisation hypothesis `harch`, formulated for the $\mathbb{R}$-algebra structures on $\mathbb{A}_{K,\infty}$ coming from the identification with the mixed space of $K$ and on $L \otimes_K \mathbb{A}_{K,\infty}$ obtained from it by $a \mapsto 1 \otimes a$, and for the Borel structure on $2\times 2$ matrices over $L \otimes_K \mathbb{A}_{K,\infty}$, requires the existence of a natural number $n_2$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly the twisted commutant $\{X : X\,\delta_\infty = \delta_\infty \cdot (\sigma \otimes \mathrm{id})(X)\}$, and such that the pushforward of $\tau_\infty'$ under the inclusion of the twisted centralizer into $M_2(L \otimes_K \mathbb{A}_{K,\infty})$ equals $s$ times the measure obtained from Lebesgue measure on $\mathbb{R}^{n_2}$ transported by $c \mapsto \sum_i c_i e_2(i)$, scaled by $\sqrt{|\det(\operatorname{Tr}_{\mathbb{R}}(\operatorname{tr}(e_2(i)e_2(j))))_{i,j}|}$ and then given the density $X \mapsto |\mathrm{N}_{\mathbb{R}}(\det X)|^{-1}$ (as an extended non-negative real, with the usual inverse convention).
--
--   The local normalisations are indexed by a function $t$ from finite places of $K$ to $[0,\infty]$ and a finite set $S_0$ of finite places, with $t_v = 1$ for $v \notin S_0$ (hypothesis `ht`). Hypothesis `hfin` requires, for each finite place $v$, one of two alternatives. Either there exists $y \in \mathrm{GL}_2(L \otimes_K K_v)$ which is a norm conjugator in the sense of [`AutomorphicForm.IsNormConjugator`](def/AutomorphicForm_TwistedOrbital.html#L214) for the local component at $v$ of the central scalar matrix with entry $u$ (its image in $\mathrm{GL}_2(K_v)$ under `AdelicLevel.glFin` followed by `AdelicLevel.finComponent`) and for $\delta_v$, that is $1 \otimes$ that scalar equals $y^{-1}\cdot(\text{norm string of } \delta_v)\cdot y$, and moreover the pushforward of $\tau_v'$ under $t \mapsto y^{-1} t y$ equals $t_v$ times the pushforward of the local Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ (normalised so that the set of matrices integral together with their inverses has measure one) along $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$; or else no scalar matrix $\mathrm{scalar}(z)$, $z$ a unit of $L \otimes_K K_v$, is $\sigma$-conjugate to $\delta_v$, and, writing $E_v$ for the set of elements of the twisted centralizer whose determinant is the image of a unit $s$ of $K_v$ with $|s|_v = 1$, one has $\tau_v'(E_v)\cdot \mathrm{N}(v) = t_v + \tau_v'(E_v)$, where $\mathrm{N}(v)$ is the absolute norm of the prime ideal $v$.
--
--   Finally, let $\tau'$ be a Haar measure (hypothesis `hτ'`) on the global twisted centralizer $T' = \{t \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K) : t\,\delta\,\sigma(t)^{-1} = \delta\}$, and let $c_{\tau'}$ be a real number with $c_{\tau'} > 0$. Hypothesis `hτ'prod` asserts that $\tau'$ decomposes as a restricted product with constant $c_{\tau'}$: for every finite set $S$ of finite places containing $S_0$ and all complex-valued functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_\infty$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $W_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$, if $W_\infty$ is almost everywhere strongly measurable on the archimedean twisted centralizer for $\tau_\infty'$, each $W_v$ with $v \in S$ is almost everywhere strongly measurable for $\tau_v'$, $W(t) = W_\infty(t_\infty)\prod_{v \in S} W_v(t_v)$ for every $t \in T'$ whose component $t_v$ lies in the semi-local integral set [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (matrices integral over the image of the semi-local integers, together with their inverses) for all $v \notin S$, and $W(t) = 0$ for every $t \in T'$ having some component $t_v \notin$ that set with $v \notin S$, then $\int_{T'} W \, d\tau' = c_{\tau'}\,\bigl(\int W_\infty \, d\tau_\infty'\bigr)\prod_{v \in S}\int W_v \, d\tau_v'$.
--
--   Let $\mathbf{v} : \mathrm{Fin}\,2 \to L$ be non-zero, let $\Psi : (\mathrm{Fin}\,2 \to \mathbb{A}_L) \to \mathbb{C}$ belong to the Schwartz–Bruhat space `schwartzBruhat2 L` (the $\mathbb{C}$-span of products of a Schwartz function on the archimedean mixed space in two variables with a locally constant compactly supported function of the finite components), and let $s_1$ be a real number with $s_1 > 1$. Write $E$ for the isomorphism $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L$ followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57) $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$. The conclusion is the finiteness of the lower Lebesgue integral
--   $$\int^-_{T'} \bigl\|\Psi\bigl(E(t)\cdot(\text{image of }\mathbf{v}\text{ in }\mathbb{A}_L^2)\bigr)\bigr\|_e \cdot \mathrm{ofReal}\bigl(\|\det E(t)\|_{\mathbb{A}_L}^{\,s_1}\bigr)\, d\tau'(t) < \infty,$$
--   where $E(t)$ acts on the column vector with entries $\mathrm{algebraMap}\,L\,\mathbb{A}_L(\mathbf{v}_i)$ by `Matrix.mulVec`, $\|\cdot\|_e$ is the extended norm on $\mathbb{C}$, and $\|\cdot\|_{\mathbb{A}_L}$ is the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of $\mathbb{A}_L$ at the given unit, raised to the real power $s_1$.
--
--   Under the stated hypotheses the twisted centralizer $T'$ is the group of adelic points of the unit group of a quaternion division algebra over $K$, the map $E$ identifies it with a subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ acting on $\mathbb{A}_L^2$, and the assertion is the absolute convergence, for exponent $s_1 > 1$, of the zeta integral of that algebra in the sense of Hey, Weil and Godement–Jacquet against an arbitrary Schwartz–Bruhat function. It feeds the computation of the behaviour of this zeta integral as the exponent tends to $1$ from above, used in the comparison of twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two.lean

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

theorem AutomorphicForm.lintegral_twistedCentralizer_enorm_mul_ideleNorm_det_rpow_lt_top_of_mem_schwartzBruhat2_of_forall_ne_scalar_of_finrank_eq_two
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
    (Ψ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 L) (s₁ : ℝ) (hs₁ : 1 < s₁) :
    ∫⁻ t, ‖Ψ (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤ := by sorry
