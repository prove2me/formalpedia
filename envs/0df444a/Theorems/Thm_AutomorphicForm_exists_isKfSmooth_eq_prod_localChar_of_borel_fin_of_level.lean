-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
-- name    : AutomorphicForm.exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f45a511c-2fc2-502e-b5e8-50be317797c9
-- title:
--   A K_f-smooth induced section with prescribed level and support
-- statement:
--   Let $K$ be a number field and let $\alpha$ denote the character of the ideles $(\mathbb{A}_K)^\times$ obtained from the distributive Haar character (module) of the adele ring, viewed as a homomorphism to $\mathbb{R}^\times$; assume $\alpha$ takes positive values. Let $s \in \mathbb{C}$, let $\nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a homomorphism which is continuous as a $\mathbb{C}$-valued function, let $S$ be a finite set of height-one primes of $\mathcal{O}_K$ and $n : \mathrm{HeightOneSpectrum}(\mathcal{O}_K) \to \mathbb{N}$ with $n_v > 0$ for $v \in S$. Assume that for $v \in S$ the local component `localChar` $\nu_v$ (the restriction of $\nu$ to the $v$-th local units, embedded into the ideles) kills every unit $t$ with $v(t-1) \le |\varpi_v|^{n_v}$, and that for $v \notin S$ the character $\nu$ is unramified at $v$, in the sense that $\nu_v(t)=1$ whenever $t$ and $t^{-1}$ both lie in $\mathcal{O}_v$. Then there exists $\Psi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ with the following seven properties. (i) $\Psi(g)$ depends only on the finite part `glFin` of $g$. (ii) For every $b$ in the adelic Borel subgroup (lower-left entry zero) with trivial archimedean part `glArch` $b = 1$, and every $g$, $\Psi(bg) = \eta_1(b_{11})\,\eta_2(b_{22})\,\Psi(g)$, where $\eta_1 = \alpha^{s+1/2}$ is `etaFst 1 α hα s` and $\eta_2 = \nu \cdot \alpha^{-(s+1/2)}$ is `etaSnd ν α hα s`, evaluated on the diagonal entries of $b$ as units. (iii) $\Psi$ is continuous. (iv) $\Psi$ is `IsKfSmooth`, i.e. a smooth vector for right translation by the subgroup of elements with trivial archimedean part. (v) $\Psi(gk) = \Psi(g)$ for every $g$ and every $k$ with trivial archimedean part whose finite part is integral (`finiteIntegralGL2`) and which satisfies $v(k_{ij} - \delta_{ij}) \le |\varpi_v|^{n_v}$ for all $i,j$ and all $v \in S$. (vi) $\Psi(g\,\iota_v(k_v)) = \Psi(g)$ for every $v \notin S$ and every $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$, mapped into $\mathrm{GL}_2(\mathbb{A}_K)$ through $\mathrm{GL}_2(K_v)$ by [`UnramifiedWhittaker.placeEmbed`](def/UnramifiedWhittaker_HeckeRecursion.html#L47). (vii) $\Psi(g) = 0$ whenever for some $v \in S$ the bottom row of $g$ fails $v(g_{10}) \le v(g_{11})\,|\varpi_v|^{n_v}$. (viii) If $k$ has integral finite part, $d$ is a family of local units with $k_{11} = d_v$ at each $v \in S$, and $v(k_{10}) \le v(k_{11})\,|\varpi_v|^{n_v}$ for all $v \in S$, then $\Psi(k) = \prod_{v \in S} \nu_v(d_v)$.
--
--   This is the construction of the non-archimedean half of a section in the principal series induced from the characters $(\,\alpha^{s+1/2},\ \nu\,\alpha^{-(s+1/2)})$ of the adelic Borel, with level prescribed by the congruence data $(S,n)$, sphericity away from $S$, support in $B K(\mathfrak{p}^{n})$ at the places of $S$, and normalised values $\prod_{v\in S}\nu_v(d_v)$ on the support. It is used in the comparison of such a section with the corresponding function on the maximal compact subgroup, by [`AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant`](thm.html#AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v)
      (_hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ,
        Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          localChar ν v t = 1)
      (_hνout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ν v),
    ∃ Ψ : AdelicGL2 (𝓞 K) K → ℂ,
      (∀ g g' : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g' → Ψ g = Ψ g') ∧
      (∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        glArch (𝓞 K) K b = 1 →
          Ψ (b * g) =
            ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
              ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * Ψ g) ∧
      Continuous Ψ ∧ IsKfSmooth K Ψ ∧
      (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        Ψ (g * k) = Ψ g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          Ψ (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Ψ g) ∧
      (∀ g : AdelicGL2 (𝓞 K) K,
        (∃ v ∈ S, ¬ Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        Ψ g = 0) ∧
      (∀ (k : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          Ψ k = ∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) := by sorry
