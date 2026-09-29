-- Prove2me | Theorems.Thm_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal
-- name    : AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/1e3f04f8-ed4f-5299-98bf-cf5b9d17ad7f
-- title:
--   Adelic matching at σ-classes with central norm, prime degree
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, $\mathbb{A}_K$ denotes the adele ring of $K$, $K_\infty$ its infinite part, $\mathbb{A}_K^{\mathrm{fin}}$ its finite part, and all groups $GL_2$ of the rings occurring carry their Borel $\sigma$-algebras (`glBorel`, [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), and the Borel structures on centralisers and twisted centralisers).
--
--   Degree and automorphism: $[L:K] = \operatorname{finrank}_K L$ is assumed prime (`hprime`) and $\sigma : L \simeq_K L$ is an automorphism with $\sigma \neq 1$ (`hσ`).
--
--   Measures and normalising constants: $\mu_K$ is a Haar measure on $GL_2(\mathbb{A}_K)$ (`hμK`), $\mu_L$ a Haar measure on $GL_2(L \otimes_K \mathbb{A}_K)$ (`hμL`), and $c_K, c_L$ are positive reals. The hypothesis `hG` states the restricted‑product formula for $\mu_K$ with constant $c_K$: for every finite set $S$ of maximal ideals of $\mathcal{O}_K$, every $f$ on $GL_2(\mathbb{A}_K)$, every $f_\infty$ on $GL_2(K_\infty)$ and every family $(f_v)$ with $f_v$ on $GL_2(K_v)$, if $f_\infty$ is a.e. strongly measurable for [`AutomorphicForm.archHaarK`](def/AutomorphicForm_TwistedOrbital.html#L401) and each $f_v$ ($v \in S$) is a.e. strongly measurable for [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168), if $f(g) = f_\infty(g_\infty)\prod_{v \in S} f_v(g_v)$ whenever all components $g_v$ with $v \notin S$ lie in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (the matrices in $GL_2(K_v)$ which together with their inverses have entries in $\mathcal{O}_v$), and $f(g) = 0$ whenever some component off $S$ fails to lie in that set, then $\int f \, d\mu_K = c_K \left(\int f_\infty \, d(\mathrm{archHaarK})\right)\prod_{v \in S}\int f_v \, d(\mathrm{localHaar})$. The hypothesis `hG'` is the exact analogue for $\mu_L$ with constant $c_L$ on $GL_2(L \otimes_K \mathbb{A}_K)$, with the archimedean factor on $GL_2(L \otimes_K K_\infty)$ measured by [`AutomorphicForm.archHaarL`](def/AutomorphicForm_TwistedOrbital.html#L412), the place‑$v$ factors on $GL_2(L \otimes_K K_v)$ measured by [`AutomorphicForm.semiLocalHaar`](def/AutomorphicForm_TwistedOrbital.html#L169) (normalised to give mass one to [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136), the matrices which together with their inverses have entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$), and the projections [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46), [`AutomorphicForm.tensorPlace`](def/AutomorphicForm_BaseChangePlaces.html#L49) in place of the adelic projections.
--
--   Ramification: $S$ is a finite set of maximal ideals of $\mathcal{O}_K$ such that for every $v \notin S$ and every maximal ideal $w$ of $\mathcal{O}_L$ lying under‑image $v$, the ramification index of $w$ over $v$ equals $1$ (`hS`).
--
--   Test functions and their factorisations: $\varphi$ on $GL_2(\mathbb{A}_L)$, $f$ on $GL_2(\mathbb{A}_K)$, together with archimedean factors $\varphi_\infty$, $f_\infty$, finite factors $\varphi_{\mathrm{fin}}$, $f_{\mathrm{fin}}$, and families $\varphi_S$ (on the groups $GL_2(L \otimes_K K_v)$) and $f_S$ (on the groups $GL_2(K_v)$). The hypothesis `hφ` is [`AutomorphicForm.IsSemiLocalFactorization`](def/AutomorphicForm_TwistedOrbital.html#L452): $\varphi_\infty$ is an archimedean test factor (given by a smooth function of the archimedean matrix entries and compactly supported), $\varphi_{\mathrm{fin}}$ is locally constant with compact support, each $\varphi_S(v)$ for $v \in S$ is locally constant with compact support, $\varphi_{\mathrm{fin}}(h) = \prod_{v \in S}\varphi_S(v)(h_v)$ whenever all semi‑local components of $h$ off $S$ lie in the semi‑local integral set, $\varphi_{\mathrm{fin}}(h) = 0$ whenever some such component does not, and $\varphi(g) = \varphi_\infty(g_\infty)\varphi_{\mathrm{fin}}(g_{\mathrm{fin}})$. The hypothesis `hf` is [`AutomorphicForm.IsUnitFactorization`](def/AutomorphicForm_TwistedOrbital.html#L526), the same list for $f$, $f_\infty$, $f_{\mathrm{fin}}$, $f_S$ over $K$, with `localIntegralSet` in place of the semi‑local integral sets.
--
--   Matching hypotheses: `hArch` asserts [`AutomorphicForm.AreMatchingArch`](def/AutomorphicForm_TwistedOrbital.html#L427) for the pair $(\varphi_\infty, f_\infty)$, that is, the relation `AreMatchingOn` at the archimedean place for $\varphi_\infty \circ \mathrm{archIdentGL}$ and $f_\infty$ with respect to `archHaarL` and `archHaarK`; `hLoc` asserts [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386) for $(\varphi_S(v), f_S(v))$ at every $v \in S$; and `hunit` asserts the same matching at every $v \notin S$ for the pair consisting of the indicator function of the semi‑local integral set and the indicator function of the local integral set. In each case `AreMatchingOn` consists of two clauses: first, for every $\delta$ whose norm string is `IsRegularSemisimple`, every regular semisimple $\gamma$, every $y$ with `IsNormConjugator` relating $\gamma$ and $\delta$, and every pair of Haar measures on the twisted centraliser of $\delta$ and the centraliser of $\gamma$ satisfying `Coupled`, any twisted orbital integral $I'$ of the $L$‑side function at $\delta$ equals any orbital integral $I$ of the $K$‑side function at $\gamma$; second, for every regular semisimple $\gamma$ admitting no $\delta$ with `IsNormOf`, every orbital integral of the $K$‑side function at $\gamma$ vanishes.
--
--   The class considered: $\delta_0 \in GL_2(L)$, $c \in (L \otimes_K \mathbb{A}_K)^\times$ and $u \in \mathbb{A}_K^\times$, and $\delta$ denotes the element $\delta_0 \otimes 1$ times the scalar matrix $c$ in $GL_2(L \otimes_K \mathbb{A}_K)$, the first factor being the image of $\delta_0$ under the map induced by $\ell \mapsto \ell \otimes 1$. The hypothesis `hN` states that the norm string of $\delta$, namely the product $\prod_{i<[L:K]} \sigma^i(\delta)$ of the iterates of `sigmaGL` applied to $\delta$ in the order $i = 0, \dots, [L:K]-1$, equals the image under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) (induced by $a \mapsto 1 \otimes a$) of the central scalar matrix $u \cdot 1$ in $GL_2(\mathbb{A}_K)$.
--
--   Measures on the centralisers and the volume growth: $\tau$ is a Haar measure on the centraliser of the scalar matrix $u \cdot 1$ in $GL_2(\mathbb{A}_K)$ and $\tau'$ a Haar measure on the twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$ in $GL_2(L \otimes_K \mathbb{A}_K)$; $C$ is a nonzero, finite element of $[0,\infty]$. The hypothesis `hD'` states: for every subset $D'$ of the twisted centraliser which is a fundamental domain, for the right action of the image in $GL_2(L \otimes_K \mathbb{A}_K)$ of the $\sigma$‑centraliser $\{t \in GL_2(L) : t\,\delta_0\,\sigma(t)^{-1} = \delta_0\}$, regarded as a subgroup of that twisted centraliser, with respect to $\tau'$, and for all reals $0 < a \le b$, the $\tau'$‑measure of the part of $D'$ where the idele norm over $L$ of the determinant of $t$, transported along the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ given by `Algebra.TensorProduct.comm` followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), lies in $[a,b]$ equals $C \cdot \log(b/a)$. The hypothesis `hD` states the corresponding statement on the $K$‑side: for every subset $D$ of the centraliser of $u \cdot 1$ which is a fundamental domain for the right action of the image of $GL_2(K)$ (the range of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15)), regarded as a subgroup of that centraliser, with respect to $\tau$, and for all $0 < a \le b$, the $\tau$‑measure of the part of $D$ where the idele norm over $K$ of $\det t$ lies in $[a,b]$ equals $[L:K] \cdot C \cdot \log(b/a)$.
--
--   The two integrals: $I, I' \in \mathbb{C}$, with `hI'` asserting [`AutomorphicForm.IsTwistedOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L287) for $\mu_L$, the class $\delta$, the measure $\tau'$ and the function $\varphi$ read on $GL_2(L \otimes_K \mathbb{A}_K)$ through the above isomorphism with $\mathbb{A}_L$, with value $I'$: there is a nonnegative measurable compactly supported $w$ on $GL_2(L \otimes_K \mathbb{A}_K)$ with $\int_{\text{twisted centraliser}} w(tx)\, d\tau' = 1$ for every $x$ at which $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$, and $I' = \int \varphi(x^{-1}\delta\,\sigma(x))\, w(x)\, d\mu_L$. The hypothesis `hI` asserts [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248) for $\mu_K$, the central scalar $u \cdot 1$, the measure $\tau$ and $f$, with value $I$: there is a nonnegative measurable compactly supported $w$ on $GL_2(\mathbb{A}_K)$ with $\int_{\text{centraliser}} w(tx)\, d\tau = 1$ for every $x$ at which $f(x^{-1}(u\cdot 1)x) \neq 0$, and $I = \int f(x^{-1}(u\cdot 1)x)\, w(x)\, d\mu_K$.
--
--   Conclusion: $c_K \cdot I' = c_L \cdot I$, the real constants being taken as complex numbers.
--
--   This is the comparison of the global twisted orbital integral of a factorisable test function at a $\sigma$-conjugacy class whose norm string is a central scalar with the corresponding orbital integral over $K$, in the form needed for cyclic base change of $GL_2$ in prime degree: the two are equal up to the measure-normalising constants $c_K$, $c_L$, the factor $[L:K]$ being absorbed by the prescribed volume growth of the fundamental domains. It feeds into [`AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization`](thm.html#AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization), which assembles the place-by-place matching of test functions into the adelic matching statement including the classes with central norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal.lean

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

theorem AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hμK : μK.IsHaarMeasure)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa
          (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) *
            ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa
          (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) *
            ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ w : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
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
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
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
              (Algebra.TensorProduct.includeLeftRingHom :
                L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom :
                  L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
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
            ({AutomorphicForm.centralScalar (𝓞 K) K u} :
              Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈
            Set.Icc a b}) =
          (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a)))
    (I I' : ℂ)
    (hI' : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I')
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK
      (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by sorry
