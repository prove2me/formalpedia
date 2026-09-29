-- Prove2me | Theorems.Thm_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
-- name    : AutomorphicForm.isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a76d302b-48c4-5d11-964b-d9431630c20b
-- title:
--   Product of local section functions is a global section function
-- statement:
--   Let $K$ be a number field and $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$, and write $g \mapsto g_\infty$ for `AdelicLevel.glArch` and $g \mapsto g_v$ for the composite of `AdelicLevel.glFin` with `AdelicLevel.finComponent` at a finite place $v$. Let $\tau$ be a measure on the centralizer of $\gamma$ in $\mathrm{GL}_2(\mathbb{A}_K)$, $\tau_\infty$ one on the centralizer of $\gamma_\infty$ in $\mathrm{GL}_2(K_\infty)$ and $\tau_v$ one on the centralizer of $\gamma_v$ in $\mathrm{GL}_2(K_v)$ for each $v$, all three carrying the Borel structure of the subspace topology; let $c > 0$ be real. Assume the restricted-product factorisation `hτ`: for every finite set $S'$ of finite places and all functions $W$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $W_\infty$ on $\mathrm{GL}_2(K_\infty)$ and $W_v$ on $\mathrm{GL}_2(K_v)$ with values in $\mathbb{C}$, such that $W_\infty$ is almost everywhere strongly measurable for $\tau_\infty$, each $W_v$ ($v \in S'$) almost everywhere strongly measurable for $\tau_v$, $W(t) = W_\infty(t_\infty)\prod_{v \in S'} W_v(t_v)$ for every $t$ in the centralizer of $\gamma$ whose components $t_v$ lie in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for all $v \notin S'$ (i.e. $t_v$ and $t_v^{-1}$ both have entries in the valuation ring of $K_v$), and $W(t) = 0$ for every such $t$ failing that condition at some $v \notin S'$, one has $\int W \,d\tau = c \cdot (\int W_\infty \,d\tau_\infty) \cdot \prod_{v \in S'} \int W_v \,d\tau_v$. Let $S$ be a finite set of finite places and let $f$, $f_\infty$, $f_v$ be complex functions on $\mathrm{GL}_2(\mathbb{A}_K)$, $\mathrm{GL}_2(K_\infty)$, $\mathrm{GL}_2(K_v)$ satisfying the same two conditions as $W$ above, but now for all $g \in \mathrm{GL}_2(\mathbb{A}_K)$ rather than only on the centralizer. Finally let $w_\infty$ and $w_v$ be real functions such that $w_\infty$ is a section function for $f_\infty$ at $\gamma_\infty$ relative to $\tau_\infty$, $w_v$ is a section function for $f_v$ at $\gamma_v$ relative to $\tau_v$ for $v \in S$, and, for $v \notin S$, the indicator of [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) is a section function for the complex indicator of that same set at $\gamma_v$ relative to $\tau_v$; here, in the sense of [`AutomorphicForm.IsSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L239), a section function for $h$ at $\gamma_0$ relative to $\nu$ is a nonnegative measurable compactly supported real function $w$ with $\int_{Z(\gamma_0)} w(tx)\,d\nu(t) = 1$ for every $x$ with $h(x^{-1}\gamma_0 x) \neq 0$. The conclusion is that the function $x \mapsto c^{-1} \, w_\infty(x_\infty) \prod_{v \in S} w_v(x_v)$, multiplied by the indicator of the set of $x$ with $x_v \in$ [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for all $v \notin S$, is a section function for $f$ at $\gamma$ relative to $\tau$ in the same sense.
--
--   This is the step that permits a global orbital integral of a factorisable function on $\mathrm{GL}_2(\mathbb{A}_K)$ to be evaluated as a product of local orbital integrals: the global section function used to cut down the orbit is itself built as a product of local ones, unit indicators at almost all finite places. It is cited by [`AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization) and [`AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (c : ℝ) (hc : 0 < c)
    (hτ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
          AutomorphicForm.localIntegralSet K v) →
        f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
          ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g)))
    (hf0 : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
          AutomorphicForm.localIntegralSet K v) → f g = 0)
    (wa : GL (Fin 2) (InfiniteAdeleRing K) → ℝ)
    (hwa : AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ) τa fa wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℝ)
    (hwf : ∀ v ∈ S, AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (wf v))
    (hunit : ∀ v ∉ S, AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℝ))) :
    AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) γ τ f
      ({x : GL (Fin 2) (AdeleRing (𝓞 K) K) |
          ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x) ∈
            AutomorphicForm.localIntegralSet K v}.indicator
        fun x => c⁻¹ * (wa (AdelicLevel.glArch (𝓞 K) K x) *
          ∏ v ∈ S, wf v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)))) := by sorry
