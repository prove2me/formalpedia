-- Prove2me | Theorems.Thm_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ea4c64fb-a096-524a-a83e-25792c77b1fb
-- title:
--   Global matching at central-norm classes of the second kind
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra of degree $2$ (hypothesis `h2`: $\operatorname{finrank}_K L = 2$), and $\sigma : L \simeq_{\mathrm{alg}[K]} L$ is an automorphism with $\sigma \neq 1$.
--
--   **Measures and factorisation constants.** $\mu_K$ is a Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ for the Borel $\sigma$-algebra [`NumberField.AdelicHaar.glBorel`](def/NumberField_AdelicHaar.html#L176), and $\mu_L$ a Haar measure on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57). Two real constants $c_K, c_L > 0$ are given, together with the two factorisation hypotheses `hG` and `hG'`. The first, `hG`, asserts: for every finite set $S$ of finite places of $K$ (elements of the height-one spectrum of $\mathcal{O}_K$), every $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, every $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and every family $f_v$ on $\mathrm{GL}_2(K_v)$, if $f_\infty$ is almost everywhere strongly measurable for [`AutomorphicForm.archHaarK`](def/AutomorphicForm_TwistedOrbital.html#L401), each $f_v$ ($v \in S$) is almost everywhere strongly measurable for [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168), the value $f(g)$ equals $f_\infty(g_\infty) \prod_{v \in S} f_v(g_v)$ whenever $g_v \in$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for all $v \notin S$, and $f(g) = 0$ as soon as $g_v \notin$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for some $v \notin S$, then $\int f \, d\mu_K = c_K \bigl(\int f_\infty \, d(\mathrm{archHaarK})\bigr) \prod_{v\in S} \int f_v \, d(\mathrm{localHaar}\,K\,v)$. Here `localIntegralSet K v` is the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in the valuation ring of $K_v$, and the components $g_\infty$, $g_v$ are taken via `AdelicLevel.glArch` and `AdelicLevel.finComponent` $\circ$ `AdelicLevel.glFin`. The second, `hG'`, is the exact analogue for $\mu_L$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, with the archimedean component taken by [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46), the component at $v$ by [`AutomorphicForm.tensorPlace K L v`](def/AutomorphicForm_BaseChangePlaces.html#L49), the reference measures [`AutomorphicForm.archHaarL`](def/AutomorphicForm_TwistedOrbital.html#L412) and [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169), the integrality condition $x_v \in$ [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (both $x_v$ and $x_v^{-1}$ having entries in [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98), the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`), and constant $c_L$.
--
--   **The finite set of places.** $S$ is a finite set of finite places of $K$ subject to `hS`: for every $v \notin S$ and every prime $w$ of $\mathcal{O}_L$ with `HeightOneSpectrum.under` $w = v$, the ramification index $e(w/v)$ equals $1$.
--
--   **Test functions and their factorisations.** Given are $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, archimedean factors $\varphi_\infty$, $f_\infty$, finite factors $\varphi_{\mathrm{fin}}$, $f_{\mathrm{fin}}$, and families $\varphi_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$, $f_v$ on $\mathrm{GL}_2(K_v)$. The hypothesis `hφ` is [`AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS`](def/AutomorphicForm_TwistedOrbital.html#L452): $\varphi_\infty$ is an archimedean test factor for $L$ (a compactly supported function of the archimedean matrix entries coming from a smooth function on the mixed space), $\varphi_{\mathrm{fin}}$ is locally constant with compact support, each $\varphi_v$ for $v \in S$ is locally constant with compact support, $\varphi_{\mathrm{fin}}(h) = \prod_{v \in S} \varphi_v(h_v)$ whenever all semi-local components $h_v$ for $v \notin S$ lie in `semiLocalIntegralSet K L v`, $\varphi_{\mathrm{fin}}(h) = 0$ if some such component fails to, and $\varphi(g) = \varphi_\infty(g_\infty)\varphi_{\mathrm{fin}}(g_{\mathrm{fin}})$. The hypothesis `hf` is [`AutomorphicForm.IsUnitFactorization K S f fa ff fS`](def/AutomorphicForm_TwistedOrbital.html#L526), the same list for $f$ over $K$, with `localIntegralSet K v` and `AdelicLevel.finComponent` in place of the semi-local data.
--
--   **Matching hypotheses.** `hArch` is [`AutomorphicForm.AreMatchingArch K L σ φa fa`](def/AutomorphicForm_TwistedOrbital.html#L427), that is `AreMatchingOn` for the base ring $\mathbb{A}_{K,\infty}$, the Haar measures `archHaarL`, `archHaarK`, the function $\varphi_\infty \circ$ `archIdentGL` and $f_\infty$: it asserts both that for every $\delta$ whose norm string `normString` is regular semisimple, every regular semisimple $\gamma$, every $y$ with `IsNormConjugator` relating $\gamma$, $\delta$, $y$, and every pair of Haar measures on the centralizer of $\gamma$ and on the twisted centralizer of $\delta$ that are `Coupled` through $y$, the corresponding twisted orbital integral and orbital integral agree, and that the orbital integral of $f_\infty$ vanishes at every regular semisimple $\gamma$ admitting no $\delta$ with `IsNormOf`. `hLoc` requires the same predicate [`AutomorphicForm.AreMatchingLocal K L v σ`](def/AutomorphicForm_TwistedOrbital.html#L386) for the pair $(\varphi_v, f_v)$ at each $v \in S$, and `hunit` requires it at each $v \notin S$ for the pair of indicator functions of `semiLocalIntegralSet K L v` and of `localIntegralSet K v` with value $1$.
--
--   **The twisted class.** Given are $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ and an idele unit $u$ of $\mathbb{A}_K$. Write $\delta$ for the element $\iota(\delta_0) \cdot \mathrm{scalar}(c)$ of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\iota$ is induced entrywise by `Algebra.TensorProduct.includeLeftRingHom`. The hypothesis `hN` states that the norm string [`AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ`](def/AutomorphicForm_TwistedOrbital.html#L205), the product $\prod_{i < \operatorname{finrank}_K L} (\mathrm{sigmaGL})^{i}(\delta)$ of the iterates of the $\sigma$-twist, equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) of the central scalar [`AutomorphicForm.centralScalar (𝓞 K) K u`](def/AutomorphicForm_AdelicLsXi.html#L18). The hypothesis `hns` states that $\delta_0$ is not $\sigma$-conjugate to a scalar over $L$: for all $x \in \mathrm{GL}_2(L)$ and all $z \in L^\times$, $x^{-1}\delta_0\,\sigma(x) \neq \mathrm{scalar}(z)$.
--
--   **Measures on the centralizers and their normalisation.** $\tau$ is a Haar measure on the centralizer of the singleton $\{\mathrm{centralScalar}\ u\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$, and $\tau'$ a Haar measure on the twisted centralizer [`AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ`](def/AutomorphicForm_TwistedOrbital.html#L220), the subgroup of those $t$ with $t\,\delta\,(\mathrm{sigmaGL}\,t)^{-1} = \delta$; both carry their Borel $\sigma$-algebras. A constant $C \in [0,\infty]$ is given with $C \neq 0$ and $C \neq \infty$, and the two hypotheses `hD'` and `hD` fix the normalisation. `hD'`: for every subset $D'$ of the twisted centralizer of $\delta$ which is a fundamental domain, with respect to $\tau'$, for the right-translation action of the subgroup obtained by transporting $\{t \in \mathrm{GL}_2(L) : t\,\delta_0\,(\sigma t)^{-1} = \delta_0\}$ into the twisted centralizer along the entrywise map induced by `Algebra.TensorProduct.includeLeftRingHom`, and for all reals $0 < a \le b$, the $\tau'$-measure of the intersection of $D'$ with the set of $t$ whose idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) of $\det t$ — the determinant being taken after transporting $t$ along the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ given by `Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57) — lies in $[a,b]$, equals $C \cdot \log(b/a)$. `hD`: for every subset $D$ of the centralizer of `centralScalar u` which is a fundamental domain, with respect to $\tau$, for the right-translation action of the range of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) (the image of $\mathrm{GL}_2(K)$) inside that centralizer, and for all $0 < a \le b$, the $\tau$-measure of the intersection of $D$ with the set of $t$ with `ideleNorm K` $(\det t) \in [a,b]$ equals $\operatorname{finrank}_K L \cdot C \cdot \log(b/a)$.
--
--   **The two integrals.** Complex numbers $I$ and $I'$ are given. The hypothesis `hI'` states [`AutomorphicForm.IsTwistedOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L287) for $\sigma$, $\mu_L$, $\delta$, $\tau'$ and the function $\varphi$ composed with the entrywise transport along $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ just described, with value $I'$: there is a weight $w \geq 0$, measurable with compact support, such that $\int_{T'} w(tx)\, d\tau' = 1$ for every $x$ at which the integrand $\varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x))$ is non-zero, and $I' = \int \varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x))\, w(x)\, d\mu_L$. The hypothesis `hI` states [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248) for $\mu_K$, $\gamma = \mathrm{centralScalar}\ u$, $\tau$, $f$ with value $I$: there is such a weight $w$ with $\int w(tx)\, d\tau = 1$ over the centralizer of $\gamma$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, and $I = \int f(x^{-1}\gamma x)\, w(x)\, d\mu_K$.
--
--   **Conclusion.** $c_K \cdot I' = c_L \cdot I$, as an identity of complex numbers, the real constants being coerced to $\mathbb{C}$. Note that the factorisation constant of $\mu_K$ multiplies the twisted integral and that of $\mu_L$ multiplies the untwisted one.
--
--   This is the degree-two case of the global comparison of a twisted orbital integral on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ with an orbital integral on $\mathrm{GL}_2(\mathbb{A}_K)$ at a class whose $\sigma$-norm is a central scalar, in the situation where the rational part $\delta_0$ of the class is not $\sigma$-conjugate to a scalar over $L$, so that its twisted centralizer is an inner form of $\mathrm{GL}_2$; the normalisation of the two Haar measures is pinned down by the logarithmic volumes of norm shells in fundamental domains for the rational points. It feeds [`AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal`](thm.html#AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal), in the base-change comparison of trace formulae for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
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

theorem AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hμK : μK.IsHaarMeasure)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v) (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉ AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v) (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) * ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ w : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hArch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    (hLoc : ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AutomorphicForm.AreMatchingLocal K L v σ
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : τ.IsHaarMeasure) (hτ' : τ'.IsHaarMeasure)
    (C : ENNReal) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          C * ENNReal.ofReal (Real.log (b / a)))
    (hD : ∀ D : Set (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      IsFundamentalDomain
        (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
          (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
          (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a)))
    (I I' : ℂ)
    (hI' : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
      (φ ∘ Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I')
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by sorry
