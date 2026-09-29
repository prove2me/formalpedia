-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- name    : AutomorphicForm.exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/99842863-47d6-5ff2-b173-c6624634a494
-- title:
--   Haar measure on adelic GL₂-centralizers factors over places
-- statement:
--   Let $K$ be a number field and $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $\mathcal{O}_K$. Three Haar measures are given, each on a centralizer subgroup carried with its subspace topology and the associated Borel $\sigma$-algebra: $\tau$ on the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$; $\tau_\infty$ on the centralizer of the archimedean component $\gamma_\infty$, the image of $\gamma$ under the map of general linear groups induced by the projection $\mathbb{A}_K \to \mathbb{A}_{K,\infty}$; and, for every height-one prime $v$ of $\mathcal{O}_K$, a measure $\tau_v$ on the centralizer of the component $\gamma_v \in \mathrm{GL}_2(K_v)$, normalised so that the set of $t$ in that centralizer with both $t$ and $t^{-1}$ having all entries in the valuation ring $\mathcal{O}_v$ has measure $1$. The assertion is the existence of a real $c > 0$, depending only on these data, such that for every finite set $S$ of height-one primes and all functions $W : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, $W_\infty : \mathrm{GL}_2(\mathbb{A}_{K,\infty}) \to \mathbb{C}$ and $W_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ the following holds: if $W_\infty$ is almost everywhere strongly measurable on the archimedean centralizer for $\tau_\infty$, if $W_v$ is almost everywhere strongly measurable on the centralizer of $\gamma_v$ for $\tau_v$ for each $v \in S$, if $W(t) = W_\infty(t_\infty)\prod_{v \in S} W_v(t_v)$ for every $t$ in the adelic centralizer whose components $t_v$ are integral in the above sense for all $v \notin S$, and if $W(t) = 0$ for every $t$ failing that integrality at some $v \notin S$, then $$\int W \, d\tau = c \cdot \Big(\int W_\infty \, d\tau_\infty\Big) \cdot \prod_{v \in S} \int W_v \, d\tau_v,$$ the integrals being Bochner integrals over the respective centralizers. No measurability hypothesis on $W$ and no integrability hypotheses are imposed.
--
--   This is the restricted-product decomposition of the centralizer $T$ of an element of $\mathrm{GL}_2(\mathbb{A}_K)$, in the form of a product formula expressing an adelic integral over $T$ as a constant times the archimedean integral and finitely many local integrals against the locally normalised Haar measures; it is the measure-theoretic input that makes a global orbital integral of a factorisable function equal to a product of local orbital integrals. It is used in the construction of matching functions on the adelic group from local matching data, namely by [`AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization`](thm.html#AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization) and [`AutomorphicForm.exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime`](thm.html#AutomorphicForm.exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem AutomorphicForm.exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ) τ)
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K γ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τf v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by sorry
