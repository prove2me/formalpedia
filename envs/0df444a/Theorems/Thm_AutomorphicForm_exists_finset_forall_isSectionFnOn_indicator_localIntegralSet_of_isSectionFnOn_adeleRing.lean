-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
-- name    : AutomorphicForm.exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/8d1c7da8-11cf-54eb-a7d8-ba421c25c904
-- title:
--   Global section function yields local section data at every place
-- statement:
--   Let $K$ be a number field and $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$ be such that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of the adele ring (the predicate [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402)). Let $\tau$ be an arbitrary measure on the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$, equipped with the Borel structure of its subspace topology, and for each finite place $v$ of $K$ let $\tau_v$ be a left-invariant measure, for the corresponding Borel structure, on the centralizer $T_v$ of the component $\gamma_v \in \mathrm{GL}_2(K_v)$, normalised so that $\tau_v$ of the part of $T_v$ lying in $\Omega_v := \{g : g$ and $g^{-1}$ have entries in $\mathcal{O}_v\}$ equals $1$. Fix a finite set $S$ of finite places, functions $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and $f_v$ on $\mathrm{GL}_2(K_v)$ for all $v$, all complex-valued, such that $f(g) = f_\infty(g_\infty)\prod_{v \in S} f_v(g_v)$ whenever $g_v \in \Omega_v$ for every $v \notin S$, and $f(g) = 0$ whenever $g_v \notin \Omega_v$ for some $v \notin S$. Assume further that there exists $w : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{R}$ which is nonnegative, measurable, of compact support and satisfies $\int_{Z(\gamma)} w(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, and that $f(x^{-1}\gamma x) \neq 0$ for at least one $x$. The conclusion is the conjunction of four assertions: (1) there is a finite set $S_1 \supseteq S$ of finite places such that for every $v \notin S_1$ the indicator function of $\Omega_v$, with values in $\mathbb{R}$, is a section function in the above sense for the $\mathbb{C}$-valued indicator function of $\Omega_v$ at $\gamma_v$ relative to $\tau_v$, i.e. it is nonnegative, measurable, of compact support, and $\int_{T_v} \mathbf{1}_{\Omega_v}(ty)\,d\tau_v(t) = 1$ for every $y$ with $y^{-1}\gamma_v y \in \Omega_v$; (2) for each $v \in S$ there is a compact $C \subseteq \mathrm{GL}_2(K_v)$ with $\{y : f_v(y^{-1}\gamma_v y) \neq 0\} \subseteq T_v \cdot C$; (3) for each $v \notin S$ there is a compact $C$ with $\{y : y^{-1}\gamma_v y \in \Omega_v\} \subseteq T_v \cdot C$; (4) there is a compact $C \subseteq \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ with $\{y : f_\infty(y^{-1}\gamma_\infty y) \neq 0\} \subseteq Z(\gamma_\infty) \cdot C$, where $Z(\gamma_\infty)$ is the centralizer of the archimedean component of $\gamma$.
--
--   This is the local input for the Euler factorisation of global (weighted) orbital integrals at a regular element: from one global section function for a factorizable test function one extracts normalised local section functions for the unit element of the Hecke algebra at almost all finite places, together with compactness of the orbit support modulo the centralizer at every place. It is used by [`AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization) and [`AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulLeftInvariant _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) _ (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
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
    (hw : ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) γ τ f w)
    (hne : ∃ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f (x⁻¹ * γ * x) ≠ 0) :
    (∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧ ∀ v ∉ S₁,
      AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℝ))) ∧
    (∀ v ∈ S, ∃ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (v.adicCompletion K) |
          fS v (y⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * y) ≠ 0} ⊆
        (AutomorphicForm.localCentralizer K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) :
          Set (GL (Fin 2) (v.adicCompletion K))) * C) ∧
    (∀ v ∉ S, ∃ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (v.adicCompletion K) |
          y⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * y ∈
            AutomorphicForm.localIntegralSet K v} ⊆
        (AutomorphicForm.localCentralizer K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) :
          Set (GL (Fin 2) (v.adicCompletion K))) * C) ∧
    (∃ C : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact C ∧
      {y : GL (Fin 2) (InfiniteAdeleRing K) |
          fa (y⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * y) ≠ 0} ⊆
        (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) :
          Set (GL (Fin 2) (InfiniteAdeleRing K))) * C) := by sorry
