-- Prove2me | Theorems.Thm_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
-- name    : AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/93f5c6da-245d-5517-a360-4871e6b5c400
-- title:
--   Adelic matching of orbital integrals for prime-degree base change on GL₂
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, all general linear groups carry the Borel $\sigma$-algebra of their topology (`glBorel`, `glBorelOf`, and, on centralisers and twisted centralisers, `centralizerBorel`, `twistedCentralizerBorel`), `adelicGLHaar (Fin 2) (𝓞 K) K` is the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, `archHaarK K` and `archHaarL K L` are the Haar measures on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_{K,\infty})$, and for a finite place $v$ of $K$, `localHaar K v` and `semiLocalHaar K L v` are the Haar measures on $\mathrm{GL}_2(K_v)$ and $\mathrm{GL}_2(L\otimes_K K_v)$ normalised so that the integral sets `localIntegralSet K v` (matrices over $\mathcal{O}_v$ whose inverse is again over $\mathcal{O}_v$) and `semiLocalIntegralSet K L v` (the same condition with respect to `semiLocalIntegers K L v`, the image of $\mathcal{O}_L\otimes$-integers in $L\otimes_K K_v$) have measure one.
--
--   The data are: the degree $\mathrm{finrank}_K L$ is prime; $\sigma : L \simeq_{\mathrm{alg}[K]} L$ with $\sigma \neq 1$; a finite set $S_K$ of finite places of $K$; the hypothesis `hS`, that every finite place $w$ of $L$ whose restriction `HeightOneSpectrum.under (𝓞 K) w` lies outside $S_K$ has ramification index $1$; a Haar measure $\mu_L$ on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$; two positive reals $c_K$, $c_L$; a nonnegative real $c_0$ with $c_0\, c_K = c_L$; and two Euler-factorisation hypotheses. The first, `hG`, states that for every finite set $S$ of finite places of $K$, every $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, every $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ that is almost everywhere strongly measurable for `archHaarK K`, and every family $f_v$ on $\mathrm{GL}_2(K_v)$ with $f_v$ almost everywhere strongly measurable for `localHaar K v` at $v\in S$, the equalities $f(g) = f_\infty(g_\infty)\prod_{v\in S} f_v(g_v)$ for all $g$ whose components outside $S$ lie in `localIntegralSet K v`, together with $f(g)=0$ whenever some component outside $S$ fails to lie there, imply
--   $$\int f \, d(\mathrm{adelicGLHaar}) = c_K \Big(\int f_\infty \, d(\mathrm{archHaarK})\Big)\prod_{v\in S}\int f_v \, d(\mathrm{localHaar}).$$
--   The second, `hG'`, is the same statement for $\mu_L$ with constant $c_L$, with the archimedean factor on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_{K,\infty})$, the finite factors on $\mathrm{GL}_2(L\otimes_K K_v)$, the projections `tensorArch K L` and `tensorPlace K L v`, and the sets `semiLocalIntegralSet K L v`.
--
--   The conclusion is asserted for every finite set $S'$ of finite places of $K$ with $S_K \subseteq S'$, every $\varphi : \mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and every $f : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ subject to two matching hypotheses. First, `AreMatchingAt K L σ S' φ f`: there exist factors $\varphi_\infty$, $\varphi_{\mathrm{fin}}$, $(\varphi_v)_v$ and $f_\infty$, $f_{\mathrm{fin}}$, $(f_v)_v$ such that `IsSemiLocalFactorization K L S' φ φa φf φS` and `IsUnitFactorization K S' f fa ff fS` hold — that is, the factors satisfy the test-function predicates `IsArchTestFactor`, `IsFinTestFactor`, `IsLocalTestFn`, `IsSemiLocalTestFn`, the finite factors are the products of the $v$-factors over $S'$ on elements integral outside $S'$ and vanish when some component outside $S'$ is not integral, and $\varphi$, $f$ are the products of their archimedean and finite factors — together with `AreMatchingArch K L σ φa fa` and `AreMatchingLocal K L v σ (φS v) (fS v)` for every $v\in S'$. Second, the unit-matching hypothesis: for every $v \notin S'$ such that every place $w$ of $L$ above $v$ has ramification index $1$, the pair consisting of the indicator of `semiLocalIntegralSet K L v` and the indicator of `localIntegralSet K v` (both with value $1$) satisfies `AreMatchingLocal K L v σ`, i.e. `AreMatchingOn` over $K_v$ with the measures `semiLocalHaar K L v` and `localHaar K v`.
--
--   Write $\Theta$ for the ring isomorphism $L\otimes_K\mathbb{A}_K \to \mathbb{A}_L$ obtained by composing `Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)` with [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), and $\Theta_*$ for the induced isomorphism of $\mathrm{GL}_2$. The conclusion is the conjunction of three assertions.
--
--   (1) `AreMatchingOn K L (AdeleRing (𝓞 K) K) σ μL (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K) (φ ∘ Θ_*) f`, which unfolds to two clauses. For all $\delta \in \mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ whose norm string `normString K L (AdeleRing (𝓞 K) K) σ δ` $=\prod_{i<[L:K]}\sigma_*^i(\delta)$ is regular semisimple (its trace squared minus four times its determinant is a unit), all regular semisimple $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$, all $y$ with $\mathrm{toTensorGL}(\gamma) = y^{-1}\,\mathrm{normString}(\delta)\,y$, all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the twisted centraliser $\{t : t\,\delta\,\sigma_*(t)^{-1}=\delta\}$ that are `Coupled` along $y$ (the push-forward of $\tau'$ under $t\mapsto y^{-1}ty$ equals the push-forward of $\tau$ under $\mathrm{toTensorGL}$), and all $I, I' \in \mathbb{C}$: if $I'$ is a twisted orbital integral of $\varphi\circ\Theta_*$ at $\delta$ with respect to $\mu_L$ and $\tau'$, and $I$ an orbital integral of $f$ at $\gamma$ with respect to $c_0\cdot$`adelicGLHaar` and $\tau$, then $I' = I$. And for every regular semisimple $\gamma$ which is not a norm (no $\delta$ satisfies `IsNormOf K L (AdeleRing (𝓞 K) K) σ γ δ`), every Haar $\tau$ on its centraliser and every $I$ which is an orbital integral of $f$ at $\gamma$: $I = 0$. Here an orbital integral is a value $I = \int f(x^{-1}\gamma x)\,w(x)\,d\mu$ for some nonnegative measurable compactly supported $w$ whose average over the centraliser is $1$ at every $x$ with $f(x^{-1}\gamma x)\neq 0$, and the twisted orbital integral is the corresponding integral of $\varphi(x^{-1}\delta\,\sigma_*(x))\,w(x)$.
--
--   (2) The central case. For every $\delta_0 \in \mathrm{GL}_2(L)$, every $c \in (L\otimes_K\mathbb{A}_K)^\times$ and every $u \in \mathbb{A}_K^\times$ such that the norm string of $\delta := \iota_*(\delta_0)\cdot\mathrm{scalar}(c)$ — where $\iota : L \to L\otimes_K\mathbb{A}_K$ is `Algebra.TensorProduct.includeLeftRingHom` — equals `toTensorGL` of the scalar matrix `centralScalar (𝓞 K) K u`: for all Haar measures $\tau$ on the centraliser of that scalar matrix in $\mathrm{GL}_2(\mathbb{A}_K)$ and $\tau'$ on the twisted centraliser of $\delta$, and every $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$, assume the following two normalisation hypotheses. (i) For every set $D'$ in the twisted centraliser of $\delta$ which is a fundamental domain, with respect to $\tau'$, for the right action (`.op`) of the image under $\iota_*$ of the $\sigma$-twisted centraliser $\{t \in \mathrm{GL}_2(L) : t\,\delta_0\,\sigma_*(t)^{-1} = \delta_0\}$, regarded as a subgroup of that twisted centraliser, and all reals $0 < a \le b$,
--   $$\tau'\big(D' \cap \{t : \mathrm{ideleNorm}\ L(\det \Theta_*(t)) \in [a,b]\}\big) = C\cdot \mathrm{ofReal}(\log(b/a)).$$
--   (ii) For every set $D$ in the centraliser of `centralScalar (𝓞 K) K u` which is a fundamental domain, with respect to $\tau$, for the right action of the range of `globalPoints (𝓞 K) K` (the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$), regarded as a subgroup of that centraliser, and all reals $0 < a \le b$,
--   $$\tau\big(D \cap \{t : \mathrm{ideleNorm}\ K(\det t) \in [a,b]\}\big) = [L:K]\cdot C\cdot \mathrm{ofReal}(\log(b/a)).$$
--   Then for all $I, I' \in \mathbb{C}$: if $I'$ is a twisted orbital integral of $\varphi\circ\Theta_*$ at $\delta$ with respect to $\mu_L$ and $\tau'$, and $I$ an orbital integral of $f$ at `centralScalar (𝓞 K) K u` with respect to $c_0\cdot$`adelicGLHaar` and $\tau$, then $I' = I$.
--
--   (3) Vanishing at central non-norms: for every $u \in \mathbb{A}_K^\times$ such that no $\delta \in \mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ satisfies `IsNormOf K L (AdeleRing (𝓞 K) K) σ (centralScalar (𝓞 K) K u) δ`, every Haar measure $\tau$ on the centraliser of `centralScalar (𝓞 K) K u`, and every $I \in \mathbb{C}$ which is an orbital integral of $f$ at that scalar matrix with respect to $c_0\cdot$`adelicGLHaar` and $\tau$, one has $I = 0$.
--
--   The scalar classes treated in (2) and (3) are not covered by (1), whose clauses are restricted to regular semisimple elements.
--
--   This is the global matching (transfer) step for cyclic base change of prime degree on $\mathrm{GL}_2$: local matching at the places of $S'$, unit matching outside, and the Euler factorisations of the two Haar measures are combined into equality of adelic twisted orbital integrals of $\varphi$ with adelic orbital integrals of $f$, at regular semisimple classes and at classes whose norm is central, together with vanishing at non-norms. The constant $c_0$ relating the two global measures is carried explicitly through the hypotheses $c_0 c_K = c_L$; a version in which $c_0$ is produced existentially is deduced from it, and the statement also feeds the comparison of the geometric terms of the two trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)

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
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
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
    (c₀ : NNReal) (hc₀ : (c₀ : ℝ) * cK = cL) :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
        AutomorphicForm.AreMatchingAt K L σ S' φ f →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) →
        AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ μL
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
          f ∧
        (∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
          AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
            AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) →
          ∀ (τ : Measure (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
            (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
            τ.IsHaarMeasure → τ'.IsHaarMeasure →
          ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
            (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
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
                  C * ENNReal.ofReal (Real.log (b / a))) →
            (∀ D : Set (Subgroup.centralizer
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
                  (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
          ∀ I I' : ℂ,
            AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
              (φ ∘ Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
            AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
              (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I) ∧
        (∀ u : (AdeleRing (𝓞 K) K)ˣ,
          (¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
              AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
                (AutomorphicForm.centralScalar (𝓞 K) K u) δ) →
          ∀ τ : Measure (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
            τ.IsHaarMeasure →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
              (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I = 0) := by sorry
