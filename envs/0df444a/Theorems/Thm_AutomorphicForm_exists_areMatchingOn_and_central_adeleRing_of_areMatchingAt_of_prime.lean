-- Prove2me | Theorems.Thm_AutomorphicForm_exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime
-- name    : AutomorphicForm.exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/36406e71-57e1-55c9-a261-efbb8df76f91
-- title:
--   Adelic matching for prime-degree cyclic base change of GL₂
-- statement:
--   Let $L/K$ be an extension of number fields with $[L:K]$ prime, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma\neq 1$, and let $S_K$ be a finite set of maximal ideals of $\mathcal O_K$ such that every maximal ideal $w$ of $\mathcal O_L$ whose contraction to $\mathcal O_K$ lies outside $S_K$ has ramification index $1$ over that contraction; let $\mu_L$ be a Haar measure on $GL_2(L\otimes_K\mathbb A_K)$ (all groups carrying their Borel structures). Then there is a nonzero $c_0\in\mathbb R_{\ge 0}$ with the following property. Let $S'\supseteq S_K$ be finite, let $\varphi:GL_2(\mathbb A_L)\to\mathbb C$ and $f:GL_2(\mathbb A_K)\to\mathbb C$ satisfy `AreMatchingAt K L σ S' φ f`, i.e. $\varphi$ and $f$ admit factorisations into an archimedean factor and a finite factor which is the product of semi-local, resp. local, factors at the places in $S'$ on the locus where all components outside $S'$ are integral and vanishes elsewhere, with the archimedean factors matching and the factors at each $v\in S'$ matching; assume also that at each $v\notin S'$ all of whose places above in $L$ are unramified, the indicator function of the semi-local integral set matches that of the local integral set. Write $\varphi^\flat$ for $\varphi$ transported to $GL_2(L\otimes_K\mathbb A_K)$ along the composite ring isomorphism $L\otimes_K\mathbb A_K\cong\mathbb A_K\otimes_K L\cong\mathbb A_L$, and $\mu_K=c_0\cdot$`adelicGLHaar`. Three conclusions hold. First, `AreMatchingOn` for $\varphi^\flat$ and $f$ relative to $\mu_L$ and $\mu_K$: for every $\delta$ with norm string $N\delta=\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)$ regular semisimple (i.e. $(\operatorname{tr})^2-4\det$ a unit), every regular semisimple $\gamma\in GL_2(\mathbb A_K)$ and $y$ with $\gamma_{L}=y^{-1}(N\delta)y$, and Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser $\{t\mid t\delta\sigma(t)^{-1}=\delta\}$ which are coupled (conjugation by $y$ pushes $\tau'$ to the image of $\tau$), any twisted orbital integral $I'$ of $\varphi^\flat$ at $\delta$ equals any orbital integral $I$ of $f$ at $\gamma$; and every orbital integral of $f$ at a regular semisimple $\gamma$ that is not such a norm vanishes. Secondly, for central classes: given $\delta_0\in GL_2(L)$, $c\in (L\otimes_K\mathbb A_K)^\times$, $u\in\mathbb A_K^\times$ with the norm string of $\delta=\delta_0\cdot c$ equal to the image of the central scalar $u$, Haar measures $\tau$ on the centraliser of that central scalar and $\tau'$ on the twisted centraliser of $\delta$, and $C\neq 0,\infty$ such that on any fundamental domain $D'$ for the right action of the image of $\{t\in GL_2(L)\mid t\delta_0\sigma(t)^{-1}=\delta_0\}$ one has $\tau'(D'\cap\{|\det|_L\in[a,b]\})=C\log(b/a)$ for all $0<a\le b$, while on any fundamental domain $D$ for the right action of the image of $GL_2(K)$ one has $\tau(D\cap\{|\det|_K\in[a,b]\})=[L:K]\,C\log(b/a)$, the twisted orbital integral of $\varphi^\flat$ at $\delta$ equals the orbital integral of $f$ at the central scalar $u$. Thirdly, if a central scalar $u$ is not a norm, then every orbital integral of $f$ at it vanishes.
--
--   This is the global matching of (twisted) orbital integrals for cyclic base change of $GL_2$ in prime degree, in the form needed for the comparison of the twisted and ordinary trace formulae: the regular semisimple classes are handled by the Euler factorisation of the integrals, and the central classes are handled by a normalisation of the volumes of the relevant fundamental domains, all with one and the same normalising constant $c_0$ for the Haar measure on $GL_2(\mathbb A_K)$. It feeds the identity comparing the sums over twisted and ordinary conjugacy classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
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

theorem AutomorphicForm.exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL) :
    ∃ c₀ : NNReal, c₀ ≠ 0 ∧
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
