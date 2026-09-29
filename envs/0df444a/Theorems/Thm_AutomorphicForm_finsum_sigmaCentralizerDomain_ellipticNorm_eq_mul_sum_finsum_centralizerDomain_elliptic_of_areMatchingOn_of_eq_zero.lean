-- Prove2me | Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
-- name    : AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f91c4439-8ec8-574d-8e17-d3229041cb70
-- title:
--   Cyclic base change: elliptic-norm twisted terms versus elliptic terms
-- statement:
--   Setting. Let $K \subseteq L$ be number fields with $L/K$ finite Galois and $[L:K] = \operatorname{finrank}_K L$ prime (`hprime`), let $\alpha, \beta$ be reals with $0 < \alpha < \beta$ (`hα`, `hαβ`), and let $\nu_{Z,L}$, $\nu_{Z,K}$ be Haar measures on the idele unit groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ (with their Borel structures). Let $D$ be an idele Galois descent datum [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous in each $\tau$. Let $\sigma \in \mathrm{Gal}(L/K)$ with $\sigma \neq 1$, and let `hgen` assert that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma^{-1}$.
--
--   Characters. $\xi_L$ is a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function is continuous (`hξc`) and which is trivial on the image of $L^\times$ (`hξt`). $\Xi$ is a finite set of homomorphisms from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, and `hΞ` characterises membership in $\Xi$: $\xi \in \Xi$ if and only if $\xi$ is continuous, trivial on the image of $K^\times$, and satisfies $\xi \circ N = \xi_L$, where $N$ is the idelic norm `(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm`, the unit map of the algebra norm attached to the base-change homomorphism $\mathbb{A}_K \to \mathbb{A}_L$.
--
--   Data over $L$. $R_L$ is a set of elements of $GL_2(L)$ contained (`hRLsub`) in the set of those $\delta$ for which the image under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the $\sigma^{-1}$-twisted conjugacy class of $\delta$ equals the conjugacy class of some $\gamma \in GL_2(K)$ lying in [`AutomorphicForm.ellipticCell K`](def/AutomorphicForm_GL2ConjugacyCells.html#L35) (the characteristic polynomial of $\gamma$ has no root in $K$) or in [`AutomorphicForm.centralCell K`](def/AutomorphicForm_GL2ConjugacyCells.html#L26) ($\gamma$ is a scalar matrix); and `hRL` asserts that each $\delta$ in that set admits a unique $\delta_0 \in R_L$ with $\delta = u \cdot (h^{-1} \delta_0 \,\sigma^{-1}(h))$ for some $h \in GL_2(L)$ and some scalar $u \in L^\times$, where $\sigma^{-1}$ acts entrywise. For each $\delta_0 \in R_L$, $\Psi_L(\delta_0)$ is contained in the determinant band $\{g : \|\det g\|_L \in [\alpha,\beta]\}$ (`hΨLs`, with $\|\cdot\|_L$ the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) and is a fundamental domain (`hΨL`) for the image in $GL_2(\mathbb{A}_L)$, under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), of the $\sigma^{-1}$-twisted centraliser $\{t \in GL_2(L) : t\,\delta_0\,\sigma^{-1}(t)^{-1} = \delta_0\}$, with respect to the restriction of the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` to that band. $\Theta$ is a fundamental domain in $(\mathbb{A}_L)^\times$ for $\nu_{Z,L}$ and the image of the subgroup $\{\sigma^{-1}(w)w^{-1} : w \in L^\times\}$ of $L^\times$ in $(\mathbb{A}_L)^\times$ (`hΘ`).
--
--   Data over $K$. $R_K$ is contained in `centralCell K ∪ ellipticCell K` (`hRKsub`), and `hRK` asserts that each $\gamma$ in that union admits a unique $\gamma_0 \in R_K$ with $\gamma = a \cdot (h^{-1}\gamma_0 h)$ for some $h \in GL_2(K)$, $a \in K^\times$. For $\gamma_0 \in R_K$, $\Psi_K(\gamma_0)$ lies in the determinant band over $K$ (`hΨKs`) and is a fundamental domain (`hΨK`) for the image under `globalPoints` of the centraliser of $\gamma_0$ in $GL_2(K)$, with respect to the restriction of `adelicGLHaar (Fin 2) (𝓞 K) K` to that band.
--
--   Constants and fibre integration. $c_0$ is a non-negative real, $\kappa > 0$, and the two hypotheses `hκl`, `hκi` express that integration over $\Theta$ against $\nu_{Z,L}$ of a function pulled back along $N$ equals $\kappa$ times integration over the range of $N$ against $\nu_{Z,K}$: for measurable $g$ with values in $[0,\infty]$ the lower integrals satisfy $\int_\Theta g(Nz)\,d\nu_{Z,L} = \kappa \int_{\operatorname{range} N} g\,d\nu_{Z,K}$, and for measurable complex $g$ the integrability of $g \circ N$ on $\Theta$ is equivalent to that of $g$ on $\operatorname{range} N$ and the Bochner integrals satisfy the same identity with factor $\kappa$.
--
--   Test functions and matching. $\varphi$ is continuous with compact support on $GL_2(\mathbb{A}_L)$, $f$ is continuous with compact support on $GL_2(\mathbb{A}_K)$. Write $\Phi$ for the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ obtained by composing `Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)` with [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57). The hypothesis `hOn` is [`AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm`](def/AutomorphicForm_TwistedOrbital.html#L324) for the measure on $GL_2(L \otimes_K \mathbb{A}_K)$ obtained by pushing `adelicGLHaar (Fin 2) (𝓞 L) L` forward along $GL_2(\Phi^{-1})$, the measure $c_0 \cdot$ `adelicGLHaar (Fin 2) (𝓞 K) K` on $GL_2(\mathbb{A}_K)$, the test function $\varphi \circ GL_2(\Phi)$ and $f$. Unfolded, it consists of two clauses: first, for all $\delta \in GL_2(L \otimes_K \mathbb{A}_K)$ whose norm string $\prod_{i<[L:K]} \sigma^{i}(\delta)$ is regular semisimple (trace$^2 - 4\det$ a unit), all regular semisimple $\gamma \in GL_2(\mathbb{A}_K)$, all $y$ with $\gamma \otimes 1 = y^{-1}(\text{norm string of }\delta)y$, and all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser of $\delta$ that are coupled (the pushforward of $\tau'$ by conjugation by $y$ agrees with the pushforward of $\tau$ along $t \mapsto t \otimes 1$), every twisted orbital integral $I'$ of $\varphi \circ GL_2(\Phi)$ at $\delta$ equals every orbital integral $I$ of $f$ at $\gamma$; second, for every regular semisimple $\gamma \in GL_2(\mathbb{A}_K)$ that is the norm of no $\delta$, every orbital integral of $f$ at $\gamma$ against $c_0 \cdot$ `adelicGLHaar` (for any Haar measure on its centraliser) vanishes. Here orbital and twisted orbital integrals are those of [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248) and [`AutomorphicForm.IsTwistedOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L287), taken with a non-negative measurable compactly supported section weight.
--
--   Vanishing hypothesis. `hvan` requires: for every $\gamma_0 \in R_K$ lying in `ellipticCell K`, every $a \in K^\times$ and every $u \in (\mathbb{A}_K)^\times$ such that the conjugacy class of $a\gamma_0$ is not in the range of [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766), and such that there exists a central unit $c \in (L \otimes_K \mathbb{A}_K)^\times$ whose norm string [`AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm`](def/AutomorphicForm_TwistedOrbital.html#L205) at the scalar matrix $c$ equals the image of the central idele $u$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71): for every Haar measure $\tau$ on the centraliser in $GL_2(\mathbb{A}_K)$ of the element `globalPoints γ₀` times the central scalar attached to $a u$, and every $I \in \mathbb{C}$ which is an orbital integral of $f$ at that element against $c_0 \cdot$ `adelicGLHaar` and $\tau$, one has $I = 0$.
--
--   Conclusion. Three assertions are made. Write, for $\delta_0 \in GL_2(L)$,
--   $$T_L(\delta_0) = n_L(\delta_0)^{-1} \int_\Theta \xi_L(z)\Big(\int_{\Psi_L(\delta_0)} \varphi\big(x^{-1}\,\delta_0\,\sigma^{-1}(z x)\big)\,d\,\mathrm{adelicGLHaar}\Big)\,d\nu_{Z,L},$$ where $\delta_0$ and $z$ are taken in $GL_2(\mathbb{A}_L)$ through `globalPoints` and `centralScalar`, the twist $\sigma^{-1}$ on $GL_2(\mathbb{A}_L)$ is [`AutomorphicForm.sigmaAdelicAct K L D σ.symm`](def/AutomorphicForm_SigmaAdelicAction.html#L14), and $n_L(\delta_0)$ is the cardinality (as a natural number, cast to $\mathbb{C}$) of the set of classes $q$ in $L^\times$ modulo $\{\sigma^{-1}(w)w^{-1}\}$ admitting a representative $u$ and an $h \in GL_2(L)$ with $u\delta_0 = h^{-1}\delta_0\,\sigma^{-1}(h)$; and, for $\xi_K$ a character of $(\mathbb{A}_K)^\times$ and $\gamma_0 \in GL_2(K)$,
--   $$T_K(\xi_K,\gamma_0) = n_K(\gamma_0)^{-1} \int_{(\mathbb{A}_K)^\times} \xi_K(z)\Big(\int_{\Psi_K(\gamma_0)} f\big(x^{-1}\,\gamma_0\,z x\big)\,d\,\mathrm{adelicGLHaar}\Big)\,d\nu_{Z,K},$$ with $n_K(\gamma_0)$ the cardinality of $\{a \in K^\times : \exists h,\ a\gamma_0 = h^{-1}\gamma_0 h\}$.
--
--   (1) The intersection of $R_L$, of the set of $\delta$ whose $\sigma^{-1}$-twisted norm class is the conjugacy class of some elliptic $\gamma \in GL_2(K)$, and of the support of $\delta_0 \mapsto T_L(\delta_0)$ is finite.
--
--   (2) For every $\xi_K \in \Xi$, the intersection of $R_K$, of `ellipticCell K`, and of the support of $\gamma_0 \mapsto T_K(\xi_K,\gamma_0)$ is finite.
--
--   (3) The finite sum of $T_L(\delta_0)$ over those $\delta_0 \in R_L$ whose $\sigma^{-1}$-twisted norm class is the class of an elliptic element of $GL_2(K)$ equals
--   $$\frac{c_0\,\kappa}{[L:K]\cdot \max(1,|\Xi|)}\ \sum_{\xi_K \in \Xi}\ \sum_{\gamma_0 \in R_K \cap \mathrm{ellipticCell}\,K} T_K(\xi_K,\gamma_0),$$ the scalar being the indicated real number viewed in $\mathbb{C}$ and the inner sums being finite sums over the stated sets.
--
--   This is the comparison, on the unfolded spectral-free side of the trace formula, of the $\sigma$-elliptic contribution of the twisted trace formula for $GL_2$ over $L$ with the elliptic contribution of the trace formula over $K$ in cyclic base change of prime degree, with its explicit constant $c_0\kappa/([L:K]\max(1,|\Xi|))$; the number-theoretic input enters only through the matching hypothesis `hOn` for the single pair $(\varphi, f)$ and through the vanishing hypothesis `hvan` for classes that are not norms. It is obtained from the corresponding statement for one pair of representatives together with the per-class version of the identity, and is cited in the assembly of the full comparison of the two trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0) :
    (RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ} ∩
      Function.support (fun δ₀ : GL (Fin 2) L =>
        ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
            ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
              Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
                h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL)).Finite ∧
    (∀ ξK ∈ Ξ, (RK ∩ AutomorphicForm.ellipticCell K ∩
      Function.support (fun γ₀ : GL (Fin 2) K =>
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK)).Finite) ∧
    (∑ᶠ δ₀ ∈ RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by sorry
