-- Prove2me | Theorems.Thm_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/48f63032-76b5-5393-8c4b-9ffb6e999acf
-- title:
--   Mass formula for the σ-twisted centralizer of δ
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$ (hypothesis `h2`), $\sigma : L \simeq_K L$ is a $K$-automorphism such that every $K$-automorphism of $L$ is an integral power of $\sigma$ (hypothesis `hgen`), $\mathbb{A}_K$ denotes `AdeleRing (𝓞 K) K`, $\mathbb{A}_{K,\infty}$ the infinite adele ring of $K$, and $K_v$ the completion of $K$ at a nonzero prime $v$ of $\mathcal{O}_K$. For a commutative $K$-algebra $A$, $\sigma$ acts on $L \otimes_K A$ through [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199), that is as $\sigma \otimes \mathrm{id}$, and entrywise on $\mathrm{GL}_2(L \otimes_K A)$ through [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202), written $g \mapsto g^{\sigma}$; the $\sigma$-twisted centralizer [`AutomorphicForm.twistedCentralizer K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L220) of $\delta \in \mathrm{GL}_2(L \otimes_K A)$ is the subgroup $\{ t : t\,\delta\,(t^{\sigma})^{-1} = \delta \}$, and [`AutomorphicForm.normString K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L205) is the product $\delta \cdot \delta^{\sigma}$ (the product of the first $\operatorname{finrank}_K L$ iterates of $\sigma$ applied to $\delta$). All the groups occurring carry the Borel $\sigma$-algebra of their topology.
--
--   The global data are an element $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ and an idele $u \in \mathbb{A}_K^{\times}$. Write $\delta$ for the element $(\delta_0 \otimes 1)\cdot c\,I_2$ of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, namely the image of $\delta_0$ under `Algebra.TensorProduct.includeLeftRingHom` times the scalar matrix attached to $c$. Two conditions are imposed on these data: the norm-string condition `hN`, that $\delta \cdot \delta^{\sigma}$ equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) (induced by $a \mapsto 1 \otimes a$) of the scalar matrix [`AutomorphicForm.centralScalar (𝓞 K) K u`](def/AutomorphicForm_AdelicLsXi.html#L18) attached to $u$; and the non-scalarity condition `hns`, that $x^{-1}\,\delta_0\,\sigma(x) \neq z\,I_2$ for every $x \in \mathrm{GL}_2(L)$ and every $z \in L^{\times}$, where $\sigma$ acts entrywise on $\mathrm{GL}_2(L)$.
--
--   The local measures and their normalisations are as follows. A Haar measure $\tau_a'$ (hypothesis `hτa'`) is given on the $\sigma$-twisted centralizer of $\delta_{\infty} :=$ [`AutomorphicForm.tensorArch K L δ`](def/AutomorphicForm_BaseChangePlaces.html#L46) in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, and for each finite place $v$ a Haar measure $\tau_f'(v)$ (hypothesis `hτf'`) on the $\sigma$-twisted centralizer of $\delta_v :=$ [`AutomorphicForm.tensorPlace K L v δ`](def/AutomorphicForm_BaseChangePlaces.html#L49) in $\mathrm{GL}_2(L \otimes_K K_v)$. A constant $s \in [0,\infty]$ and the hypothesis `harch` normalise $\tau_a'$: with $\mathbb{A}_{K,\infty}$ made an $\mathbb{R}$-algebra through the identification with the mixed space of $K$ and $L \otimes_K \mathbb{A}_{K,\infty}$ through $a \mapsto 1 \otimes a$, and with $M_2(L \otimes_K \mathbb{A}_{K,\infty})$ given its Borel structure, there exist $n_2 \in \mathbb{N}$ and an $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{A}_{K,\infty})$ whose $\mathbb{R}$-span is exactly the set $\{ X : X\,\delta_{\infty} = \delta_{\infty}\,X^{\sigma}\}$ (entrywise $\sigma$ on $X$), such that the image of $\tau_a'$ under the inclusion of the twisted centralizer into $M_2(L \otimes_K \mathbb{A}_{K,\infty})$ equals $s$ times the measure obtained as follows: take the image of Lebesgue measure on $\mathbb{R}^{n_2}$ under $(c_i) \mapsto \sum_i c_i e_2(i)$, scale it by $\sqrt{|\det G|}$ where $G_{ij} = \operatorname{Tr}_{(L \otimes_K \mathbb{A}_{K,\infty})/\mathbb{R}}\bigl(\operatorname{tr}(e_2(i)\,e_2(j))\bigr)$, and multiply by the density $X \mapsto |N_{(L \otimes_K \mathbb{A}_{K,\infty})/\mathbb{R}}(\det X)|^{-1}$.
--
--   A function $t$ from the finite places of $K$ to $[0,\infty]$ and a finite set $S_0$ of finite places are given with $t_v = 1$ for $v \notin S_0$ (hypothesis `ht`). The hypothesis `hfin` normalises $\tau_f'(v)$ at every finite place $v$ by a disjunction of two alternatives. In the first, there is $y \in \mathrm{GL}_2(L \otimes_K K_v)$ with [`AutomorphicForm.IsNormConjugator K L (K_v) σ`](def/AutomorphicForm_TwistedOrbital.html#L214) holding for the local component at $v$ of the scalar matrix attached to $u$ and for $\delta_v$ with conjugator $y$, that is the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of that local scalar matrix equals $y^{-1}\,\delta_v\,\delta_v^{\sigma}\,y$, and moreover the image of $\tau_f'(v)$ under $t \mapsto y^{-1} t y$ equals $t_v$ times the image under [`AutomorphicForm.toTensorGL K L (K_v)`](def/AutomorphicForm_TwistedOrbital.html#L71) of the Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$, the latter being normalised to give the compact set `localIntegralSet K v` mass one. In the second alternative, $\delta_v$ is not $\sigma$-conjugate to any scalar, i.e. for no $z \in (L \otimes_K K_v)^{\times}$ does there exist $x$ with $z\,I_2 = x^{-1}\,\delta_v\,x^{\sigma}$, and, writing $E_v$ for the set of elements $t$ of the twisted centralizer whose determinant is the image under $a \mapsto 1 \otimes a$ of a unit $s$ of $K_v$ with $\mathrm{Valued.v}(s) = 1$, one has $\tau_f'(v)(E_v) \cdot \#(\mathcal{O}_K/v) = t_v + \tau_f'(v)(E_v)$, where $\#(\mathcal{O}_K/v)$ is `Ideal.absNorm v.asIdeal`.
--
--   Globally, a Haar measure $\tau'$ (hypothesis `hτ'`) is given on $T' :=$ the $\sigma$-twisted centralizer of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, together with a real number $c_{\tau'} > 0$ and the factorisation hypothesis `hτ'prod`: for every finite set $S$ of finite places containing $S_0$ and all complex-valued functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ and $W_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$, if $W_a$ is almost everywhere strongly measurable for $\tau_a'$ on the archimedean twisted centralizer, each $W_{S,v}$ for $v \in S$ is almost everywhere strongly measurable for $\tau_f'(v)$, and if $W(t) = W_a(t_{\infty}) \prod_{v \in S} W_{S,v}(t_v)$ for every $t \in T'$ whose component $t_v$ lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for all $v \notin S$ (that is, $t_v$ and $t_v^{-1}$ have entries in the image of the semilocal integers of $L \otimes_K K_v$), while $W(t) = 0$ for every $t \in T'$ having some $v \notin S$ with $t_v$ outside that set, then $\int W \,\mathrm{d}\tau' = c_{\tau'} \bigl(\int W_a \,\mathrm{d}\tau_a'\bigr) \prod_{v \in S} \int W_{S,v} \,\mathrm{d}\tau_f'(v)$.
--
--   Finally a constant $R' \in [0,\infty]$ is given with the covolume-rate hypothesis `hD'`: let $\Gamma'$ be the image in $T'$ of the subgroup [`AutomorphicForm.sigmaCentralizer`](def/AutomorphicForm_SigmaCentralizer.html#L10) of $\mathrm{GL}_2(L)$ for $\sigma$ acting entrywise and for $\delta_0$, namely $\{x \in \mathrm{GL}_2(L) : x\,\delta_0\,\sigma(x)^{-1} = \delta_0\}$, transported by `Algebra.TensorProduct.includeLeftRingHom` and viewed as a subgroup of $T'$ via `Subgroup.subgroupOf`; then for every subset $D'$ of $T'$ which is a fundamental domain for the right action of $\Gamma'$ (its opposite subgroup) with respect to $\tau'$, and for all reals $0 < a \le b$,
--   $$\tau'\Bigl(D' \cap \bigl\{ t : \|\det t\|_{\mathbb{A}_L} \in [a,b] \bigr\}\Bigr) = R' \cdot \log(b/a),$$
--   where $t$ is first transported to $\mathrm{GL}_2(\mathbb{A}_L)$ by the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ obtained by composing `Algebra.TensorProduct.comm` with [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), its determinant is taken in $\mathbb{A}_L^{\times}$, and $\|\cdot\|_{\mathbb{A}_L}$ is [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), the module of an idele measured by `distribHaarChar`.
--
--   The conclusion is the single identity in $[0,\infty]$
--   $$2R' = c_{\tau'} \cdot s \cdot 2^{2\,[K:\mathbb{Q}]} \cdot \Bigl(\prod_{v \in S_0} t_v\Bigr) \cdot \bigl( d_K^{2} \cdot \Re\,\zeta_K(2) \cdot \operatorname{Res}_{s=1}\zeta_K \bigr),$$
--   where $[K:\mathbb{Q}] = \operatorname{finrank}_{\mathbb{Q}} K$, $d_K$ is `NumberField.discr K`, $\Re\,\zeta_K(2)$ is the real part of `NumberField.dedekindZeta K 2`, $\operatorname{Res}_{s=1}\zeta_K$ is `NumberField.dedekindZeta_residue K`, and $c_{\tau'}$ together with the final real bracket are inserted into $[0,\infty]$ by `ENNReal.ofReal`.
--
--   This is the mass, or covolume, formula for the global $\sigma$-twisted centralizer of $\delta$ modulo its group of $L$-rational points: an instance of the statement that the Tamagawa number of the multiplicative group of a quaternion division algebra over a number field is one, in the form of Eichler's mass formula, expressed for the local normalisations fixed by the hypotheses `harch`, `hfin` and `hτ'prod`. It determines the rate $R'$ at which a fundamental domain for $\Gamma'$ in $T'$ accumulates volume in the idele-norm bands of the determinant, and is cited by [`AutomorphicForm.mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
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

    (R' : ENNReal)
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          R' * ENNReal.ofReal (Real.log (b / a))) :
    2 * R' = ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
      ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
        NumberField.dedekindZeta_residue K) := by sorry
