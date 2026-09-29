-- Prove2me | Theorems.Thm_AutomorphicForm_measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
-- name    : AutomorphicForm.measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/39bc4227-790f-5724-af7e-6891efb8083d
-- title:
--   Unit mass and Euler product for twisted centralizer integrals
-- statement:
--   Let $K\subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, and $\delta \in \mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$. For a topological $K$-algebra $A$ write $T'(A)$ for the $\sigma$-twisted centralizer $\{t \mid t\,\delta_A\,\sigma(t)^{-1}=\delta_A\}$ inside $\mathrm{GL}_2(L\otimes_K A)$, where $\sigma$ acts through the factor $L$, carrying the Borel $\sigma$-algebra of its subspace topology; the relevant $\delta_A$ are the images `tensorArch` $\delta$ in $\mathrm{GL}_2(L\otimes_K\mathbb{A}_{K,\infty})$ and `tensorPlace` $v$ $\delta$ in $\mathrm{GL}_2(L\otimes_K K_v)$ for finite places $v$ of $K$. Assume given a Haar measure $\tau_a$ on the archimedean twisted centralizer, Haar measures $\tau_v$ on the local ones, an arbitrary measure $\tau$ on $T'(\mathbb{A}_K)$, a real $c>0$ and a finite set $S_0$ of finite places such that the restricted-product identity $\int W\,d\tau = c\,(\int W_\infty\,d\tau_a)\prod_{v\in S}\int W_v\,d\tau_v$ holds (Bochner integrals) for every finite $S\supseteq S_0$ and all complex functions $W$, $W_\infty$, $W_v$ with $W_\infty$ a.e. strongly measurable for $\tau_a$, each $W_v$ ($v\in S$) a.e. strongly measurable for $\tau_v$, $W(t)=W_\infty(t_\infty)\prod_{v\in S}W_v(t_v)$ whenever $t_v$ lies in `semiLocalIntegralSet` $v$ for all $v\notin S$, and $W(t)=0$ whenever some $v\notin S$ has $t_v\notin$ `semiLocalIntegralSet` $v$; here `semiLocalIntegralSet` $v$ consists of the $g\in\mathrm{GL}_2(L\otimes_K K_v)$ such that the entries of both $g$ and $g^{-1}$ lie in the image of $\mathcal{O}_L\otimes\mathcal{O}_v$ in $L\otimes_K K_v$. Assume further a finite set $S_1$, measurable $[0,\infty]$-valued $F_\infty$ on the archimedean centralizer and $F_v$ on the local centralizers, with $F_v \equiv 1$ on `semiLocalIntegralSet` $v$ for $v\notin S_1$, and $F$ on $T'(\mathbb{A}_K)$ with $F(t)=F_\infty(t_\infty)\prod_{v\in S}F_v(t_v)$ for every finite $S\supseteq S_1$ and every $t$ whose components at $v\notin S$ lie in `semiLocalIntegralSet` $v$. Then $\tau_v$ of the set of points of the local twisted centralizer lying in `semiLocalIntegralSet` $v$ equals $1$ for every $v\notin S_0$, and the net $S\mapsto c\,(\int^- F_\infty\,d\tau_a)\prod_{v\in S}\int^- F_v\,d\tau_v$ of lower Lebesgue integrals converges, along the filter of finite sets of finite places ordered by inclusion, to $\int^- F\,d\tau$.
--
--   This is the integration theory of a restricted product measure in the shape needed for Euler products: the local factors away from the exceptional set have unit mass, and the integral of a non-negative factorisable integrand is the limit of the partial products of local integrals. It is used in the computation of adelic twisted orbital and zeta integrals on the twisted centralizer, in particular in the evaluation of an integral against a power of the idele norm of the determinant and in the pairing of Haar measures with archimedean Schwartz data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology ENNReal

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.measure_semiLocalIntegralSet_eq_one_and_tendsto_prod_lintegral_twistedCentralizer_of_forall_integral_eq_mul_prod_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ)))
    (hτa : τa.IsHaarMeasure)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v, (τf v).IsHaarMeasure)
    (τ : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (c : ℝ) (hc : 0 < c) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ) => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ) => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hFa : Measurable fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ) => Fa t)
    (Ff : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞)
    (hFf : ∀ v, Measurable fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) => Ff v t)
    (hunit : ∀ v ∉ S₁, ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ),
      (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v → Ff v t = 1)
    (F : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ → ℝ≥0∞)
    (hF : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₁ ⊆ S →
      ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
        (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
          F t = Fa (AutomorphicForm.tensorArch K L t) * ∏ v ∈ S, Ff v (AutomorphicForm.tensorPlace K L v t)) :
    (∀ v ∉ S₀, τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) ∧
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
        ENNReal.ofReal c * (∫⁻ t, Fa t ∂τa) * ∏ v ∈ S, ∫⁻ t, Ff v t ∂(τf v))
      atTop (𝓝 (∫⁻ t, F t ∂τ)) := by sorry
