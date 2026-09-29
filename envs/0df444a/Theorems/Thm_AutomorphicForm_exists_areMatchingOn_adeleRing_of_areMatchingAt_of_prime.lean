-- Prove2me | Theorems.Thm_AutomorphicForm_exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime
-- name    : AutomorphicForm.exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9045912c-3b46-52e6-8b26-24509127ec0a
-- title:
--   Adelic matching of orbital integrals in prime-degree base change
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]$ prime, let $\sigma$ be an automorphism of $L$ over $K$ with $\sigma \neq 1$, and let $S_K$ be a finite set of height-one primes of $\mathcal{O}_K$ such that every height-one prime $w$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ lies outside $S_K$ has ramification index $1$. Let $\mu_L$ be a Haar measure on $GL_2(L \otimes_K \mathbb{A}_K)$, for the Borel structure of its topology. Then there is a nonzero $c_0 \in \mathbb{R}_{\geq 0}$ with the following property: for every finite $S' \supseteq S_K$ and all $\varphi : GL_2(\mathbb{A}_L) \to \mathbb{C}$, $f : GL_2(\mathbb{A}_K) \to \mathbb{C}$ such that $\varphi$ and $f$ match at $S'$ (they admit an archimedean factor, a finite factor and local factors $\varphi_v$, $f_v$ witnessing `IsSemiLocalFactorization` and `IsUnitFactorization`, with matching archimedean factors and `AreMatchingLocal` at each $v \in S'$), and such that at each $v \notin S'$ all of whose primes in $L$ are unramified the indicator of the semi-local set $\{g \in GL_2(L \otimes_K K_v) : g, g^{-1} \text{ integral}\}$ matches the indicator of $\{g \in GL_2(K_v) : g, g^{-1} \text{ integral}\}$, the transported function $\varphi' = \varphi \circ GL_2(\text{comm} \cdot \mathtt{genuineRingEquiv})$ and $f$ satisfy `AreMatchingOn` for $\mu_L$ and $c_0 \cdot$ `adelicGLHaar`: for every $\delta$ with regular semisimple norm-string (i.e. $\mathrm{tr}^2 - 4\det$ a unit), every regular semisimple $\gamma$, every norm-conjugator $y$ and every pair of Haar measures on the centraliser of $\gamma$ and the $\sigma$-twisted centraliser of $\delta$ coupled by $y$, any twisted orbital integral value of $\varphi'$ at $\delta$ equals any orbital integral value of $f$ at $\gamma$; and any orbital integral value of $f$ at a regular semisimple $\gamma$ with no norm vanishes.
--
--   This is the passage from local to global matching in cyclic base change for $GL_2$: the Euler factorisation of global orbital and twisted orbital integrals of factorisable test functions, yielding adelic matching up to one Haar normalisation constant. It is used in the comparison of the twisted elliptic term of the trace formula with the corresponding sum over elliptic classes for $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime
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
          f := by sorry
