-- Prove2me | Theorems.Thm_AutomorphicForm_exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension
-- name    : AutomorphicForm.exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/bf31dd2b-dbe9-54b5-a3e3-d75b78780603
-- title:
--   Transport of semi-local GL₂ data at an inert place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ whose degree $[L:K]$ is a prime number, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ such that every prime $w$ of $\mathcal{O}_L$ lying under $v$ has ramification index $1$ over $v$, such that the type of primes of $\mathcal{O}_L$ lying over $v$ is a subsingleton; let $w$ be one such prime. Then there exist a $K_v$-algebra isomorphism $\Phi : L \otimes_K K_v \to L_w$, a group isomorphism $e : GL_2(L_w) \to GL_2(L \otimes_K K_v)$ and a $K_v$-algebra automorphism $\theta$ of $L_w$ with all of the following. Entrywise, $(e\,x)_{pq} = \Phi^{-1}(x_{pq})$; $\Phi$ intertwines $\sigma \otimes \mathrm{id}$ with $\theta$; $\Phi(1 \otimes t)$ is the image of $t \in K_v$ under the structure map; $x$ lies in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}$ in $L \otimes_K K_v$ if and only if $\Phi x$ is an integer of $L_w$; $\theta$ has order $[L_w:K_v]$, and $[L_w:K_v] = [L:K]$; $w$ has ramification index $1$ over $v$; there is $y \in L_w$ with $\|y\| \le 1$ and $\|\theta y - y\| = 1$. Moreover $e$ is the semi-local component at $v$ of the embedding of $GL_2(L_w)$ into $GL_2$ of the finite adeles of $L$ at $w$; $e$ carries the set of matrices in $GL_2(L_w)$ that are integral together with their inverses onto the corresponding set over the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$; $e$ intertwines $GL_2(\theta)$ with the $\sigma$-twist $\mathrm{sigmaGL}$; $e$ composed with $GL_2$ of $K_v \to L_w$ is the base-change map $\mathrm{toTensorGL}$ on $GL_2(K_v)$; the semi-local weight (the finite sum of local weights over the places above $v$) of $e\,x$ equals the local weight of $x$; $e$ pushes the normalised Haar measure $\mathrm{localHaar}$ on $GL_2(L_w)$ forward to $\mathrm{semiLocalHaar}$ on Borel sets; and $e$ and $e^{-1}$ are continuous. Finally, twisted weighted orbital data transport: for every $\delta \in GL_2(L \otimes_K K_v)$, every Haar measure $\tau'$ on the $\sigma$-twisted centraliser $\{t : t\delta\,\mathrm{sigmaGL}(t)^{-1} = \delta\}$ giving mass $1$ to its integral points, and every $\varphi$ and $J'$ with $J'$ a twisted weighted orbital integral of $\varphi$ at $\delta$ against $\tau'$, there exist a Haar measure $\tau_E$ on the $\theta$-twisted centraliser of $e^{-1}\delta$ in $GL_2(L_w)$ giving mass $1$ to the integral points, and a nonnegative Borel-measurable compactly supported $s_E$ on $GL_2(L_w)$, such that $\int s_E(ty)\,d\tau_E = 1$ whenever $\varphi(e(y^{-1}(e^{-1}\delta)\,GL_2(\theta)y)) \neq 0$, and $J' = \int \varphi(e(y^{-1}(e^{-1}\delta)\,GL_2(\theta)y))\cdot \mathrm{weight}(y)\cdot s_E(y)\, d\,\mathrm{localHaar}$.
--
--   This packages, in a single statement, the classical identification $L \otimes_K K_v \cong L_w$ at a prime $v$ that is unramified with a unique prime above it in a degree-$\ell$ extension, together with everything needed to move Haar measures, integrality conditions, weights, the $\sigma$-twist and twisted weighted orbital integrals between the semi-local group $GL_2(L \otimes_K K_v)$ and $GL_2(L_w)$. It is used by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank) in the base-change comparison at inert places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L))) (w : v.Extension (𝓞 L)) :
    ∃ (Φ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (e : GL (Fin 2) (w.1.adicCompletion L) ≃* GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),

      (∀ (x : GL (Fin 2) (w.1.adicCompletion L)) (p q : Fin 2),
        ((e x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q =
          Φ.symm ((x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) p q)) ∧

      (∀ x : L ⊗[K] v.adicCompletion K, Φ (sigmaTensor K L (v.adicCompletion K) σ x) = θ (Φ x)) ∧
      (∀ t : v.adicCompletion K, Φ ((1 : L) ⊗ₜ[K] t) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t) ∧
      (∀ x : L ⊗[K] v.adicCompletion K, x ∈ semiLocalIntegers K L v ↔ Φ x ∈ w.1.adicCompletionIntegers L) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 ∧
      (∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1) ∧

      (∀ g : GL (Fin 2) (w.1.adicCompletion L),
        semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 g) = e g) ∧
      e '' localIntegralSet L w.1 = semiLocalIntegralSet K L v ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L),
        sigmaGL K L (v.adicCompletion K) σ (e x) = e (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x)) ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        toTensorGL K L (v.adicCompletion K) g =
          e (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) g)) ∧
      (∀ x : GL (Fin 2) (w.1.adicCompletion L), semiLocalWeight K L v (e x) = LocalWeight.weight x) ∧

      (∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
          (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
            (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
          (_ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
          (_ : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v} = 1)
          (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (J' : ℂ),
          IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φ J' →
          ∃ (τE : @Measure (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (e.symm δ))
              (borel _)) (sE : GL (Fin 2) (w.1.adicCompletion L) → ℝ),
            @Measure.IsHaarMeasure _ _ _ (borel _) τE ∧
            τE {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ localIntegralSet L w.1} = 1 ∧
            (∀ y, 0 ≤ sE y) ∧ Measurable[localGLBorel L w.1] sE ∧ HasCompactSupport sE ∧
            (∀ y : GL (Fin 2) (w.1.adicCompletion L),
              φ (e (y⁻¹ * e.symm δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) ≠ 0 →
                ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (e.symm δ),
                    sE ((t : GL (Fin 2) (w.1.adicCompletion L)) * y) ∂τE = 1) ∧
            J' = ∫ y : GL (Fin 2) (w.1.adicCompletion L),
                φ (e (y⁻¹ * e.symm δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) *
                  ((LocalWeight.weight y : ℝ) : ℂ) * (sE y : ℂ) ∂(localHaar L w.1)) ∧
      (∀ s : Set (GL (Fin 2) (w.1.adicCompletion L)), MeasurableSet[localGLBorel L w.1] s →
        semiLocalHaar K L v (e '' s) = localHaar L w.1 s) ∧
      Continuous e ∧ Continuous e.symm := by sorry
