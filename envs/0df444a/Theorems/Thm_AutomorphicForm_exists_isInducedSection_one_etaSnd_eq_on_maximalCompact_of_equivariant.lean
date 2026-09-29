-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
-- name    : AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/58f38a79-2af9-56ea-a763-c058de739a0c
-- title:
--   Adelic GL₂ induced sections with prescribed K-type and support
-- statement:
--   Let $K$ be a number field and let $\alpha:(\mathbb{A}_K)^\times\to\mathbb{R}^\times$ be the character obtained from the distributive Haar character of the adele ring $\mathbb{A}_K$ (the module of multiplication by an idele), pushed from $\mathbb{R}_{\ge 0}$ into $\mathbb{R}^\times$; assume $\alpha$ takes positive values. Given $s\in\mathbb{C}$ and a continuous character $\nu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ with $|\nu(x)|=1$ for all $x$ and $\nu$ trivial on the image of $K^\times$; a finite set $S$ of finite places and $n:\mathrm{Spec}^1(\mathcal{O}_K)\to\mathbb{N}$ with $n_v>0$ for $v\in S$, such that for $v\in S$ the local character $t\mapsto\nu(\iota_v t)$ is trivial on all units $t$ of $K_v$ with $v(t-1)\le q_v^{-n_v}$, and for $v\notin S$ it is trivial on all $t$ with $t$ and $t^{-1}$ integral; and a continuous function $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_K)$ that is archimedean $K$-finite (at each infinite place $w$ its right translates under the row-isometry subgroup at $w$ span a finite-dimensional space) and satisfies $f_\infty(mk)=\nu(m_{22})f_\infty(k)$ whenever $m,k$ have trivial finite components and row-isometric components at every infinite place and $m_{10}=0$. Then there is $\varphi_0:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ such that: (i) $\varphi_0(bg)=\alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\varphi_0(g)$ for every $b$ with $b_{10}=0$ and every $g$; (ii) $\varphi_0$ is continuous, archimedean $K$-finite, and $K_f$-smooth, i.e. its stabiliser for right translation inside the kernel of the archimedean-component map is open; (iii) $\varphi_0(gk)=\varphi_0(g)$ for every $k$ with trivial archimedean component whose finite part and its inverse are integral and which satisfies $v((k-1)_{ij})\le q_v^{-n_v}$ for all $i,j$ and all $v\in S$; (iv) $\varphi_0$ is right invariant under the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of $\mathrm{GL}_2(\mathcal{O}_v)$ for every $v\notin S$; (v) $\varphi_0(g)=0$ as soon as $v(g_{10})\le v(g_{11})\,q_v^{-n_v}$ fails for some $v\in S$; (vi) $\varphi_0(k)=f_\infty(k)$ for $k$ with trivial finite component and row-isometric components at all infinite places; and (vii) if $k$ has integral finite part (with integral inverse) and row-isometric archimedean components, $k_{\infty}$ has trivial finite component and the same archimedean component as $k$, and for $v\in S$ one has $k_{11}=d_v$ at $v$ with $v(k_{10})\le v(k_{11})q_v^{-n_v}$, then $\varphi_0(k)=\bigl(\prod_{v\in S}\nu_v(d_v)\bigr)f_\infty(k_\infty)$.
--
--   This is the existence statement for a global section of the induced (principal series) representation of $\mathrm{GL}_2(\mathbb{A}_K)$ attached to the pair of characters $(\|\cdot\|^{s+1/2},\,\nu\|\cdot\|^{-(s+1/2)})$, with prescribed restriction to the archimedean maximal compact, prescribed congruence level and small support at the places of $S$, and spherical behaviour outside $S$. It is used in the construction of test data for the Rankin–Selberg integral, where the last clause makes the non-vanishing of $\varphi_0$ visible from that of $f_\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνu : IsUnitaryChar (𝓞 K) K ν) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v)
      (_hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ,
        Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          localChar ν v t = 1)
      (_hνout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ν v)
      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf) (_hfK : IsArchKFinite K finf)
      (_hfeq : ∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          finf (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * finf k),
    ∃ φ₀ : AdelicGL2 (𝓞 K) K → ℂ,
      IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) φ₀ ∧
      Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧ IsKfSmooth K φ₀ ∧

      (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ₀ (g * k) = φ₀ g) ∧

      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          φ₀ (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ₀ g) ∧

      (∀ g : AdelicGL2 (𝓞 K) K,
        (∃ v ∈ S, ¬ Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ₀ g = 0) ∧

      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          φ₀ k = finf k) ∧

      (∀ (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ₀ k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf) := by sorry
