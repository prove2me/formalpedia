-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family
-- name    : AutomorphicForm.exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f2efbb78-dcec-5496-9dc8-4bd9f4367c91
-- title:
--   Normalised Weyl intertwining integral on K: continuation past Re s=0
-- statement:
--   Let $K$ be a number field, and let $\alpha$ be the idelic modulus character $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring, the adele ring carrying its Borel $\sigma$-algebra; it is assumed that $\alpha$ takes positive values. Let $\mu,\nu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be characters which are unitary ($|\mu(x)|=1$ for all $x$), trivial on the principal ideles $K^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\tau^\mu,\tau^\nu \colon \mathrm{InfinitePlace}(K)\to\mathbb{R}$ and $m^\mu,m^\nu \colon \mathrm{InfinitePlace}(K)\to\mathbb{Z}$ be such that at each infinite place $v$, writing $\mu_v$ for $\mu$ composed with the embedding of $(K_v)^\times$ as ideles trivial away from $v$: $\mu_v(x) = \|x\|_{\mathbb{A}}^{i\tau^\mu_v}$ whenever $x$ maps to a positive real, and $\mu_v(x) = x^{m^\mu_v}$ whenever $x$ maps to an element of absolute value $1$; likewise for $\nu$ with $\tau^\nu, m^\nu$. Let $\psi \colon \mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a family such that for every $s$ the function $\psi_s$ satisfies $\psi_s(bg) = \eta_1(b_{11})\eta_2(b_{22})\psi_s(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero), where $\eta_1 = \mu\cdot\alpha^{s+1/2}$ and $\eta_2 = \nu\cdot\alpha^{-(s+1/2)}$; each $\psi_s$ is archimedean $K$-finite (at each infinite place the right translates under the row-isometry subgroup of $\mathrm{GL}_2(K_v)$, included adelically, span a finite-dimensional space) and $K_f$-smooth (its stabiliser under right translation inside the kernel of the archimedean projection is open); $(s,g)\mapsto\psi_s(g)$ is continuous; $s\mapsto\psi_s(g)$ is differentiable for each $g$; and at each infinite place $v$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup containing $k\mapsto\psi_s(gk)$ for all $s$ and $g$. Put $\chi=\mu\nu^{-1}$, let $P(w)$ be the infinite product over finite places $v$ of $(1 - c_v N(v)^{-w})^{-1}$ with $c_v = \chi(\varpi_v)$ at the places where $\chi$ is unramified (trivial on the local units) and $c_v = 0$ elsewhere, let $$\gamma(w)=\prod_{v\ \mathrm{real}}\Gamma_{\mathbb{R}}\!\left(w+i(\tau^\mu_v-\tau^\nu_v)+(|m^\mu_v-m^\nu_v| \bmod 2)\right)\prod_{v\ \mathrm{complex}}\Gamma_{\mathbb{C}}\!\left(w+i(\tau^\mu_v-\tau^\nu_v)+\tfrac{|m^\mu_v-m^\nu_v|}{2}\right),$$ and let $c$ be the reciprocal of the adelic Haar volume of the adelic box. Then there exist $\delta>0$ and $R \colon \mathbb{C}\to \mathbf{K}\to\mathbb{C}$, where $\mathbf{K}$ is the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ whose finite part is integral of level $1$ and whose component at every infinite place is a row isometry, such that: $s\mapsto R(s,k)$ is analytic on a neighbourhood of $\{\mathrm{Re}\,s>-\delta\}$ for each $k$; $(s,k)\mapsto R(s,k)$ is continuous on $\{\mathrm{Re}\,s>-\delta\}\times\mathbf{K}$; for $\mathrm{Re}\,s>1/2$ and all $k$, $$\gamma(2s)P(2s)R(s,k) = \gamma(2s+1)P(2s+1)\cdot c\cdot \int_{\mathbb{A}_K}\psi_s(w^{-1}n(x)k)\,dx,$$ with $w$ the global Weyl element, $n(x)$ the upper unipotent and the integral taken against the adelic Haar measure; and there is an entire $B$ with $B(s)\neq 0$ for $\mathrm{Re}\,s>-\delta$ such that for every $k$ the function $s\mapsto B(s)R(s,k)$ agrees on $\{\mathrm{Re}\,s>-\delta\}$ with an entire function.
--
--   This is the Langlands–Shahidi normalisation of the $\mathrm{GL}_2$ intertwining operator $M(s)$ on the induced representation attached to $(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$, restricted to the adelic maximal compact subgroup: after dividing by the completed Dirichlet series $\gamma(2s)P(2s)$ of $\chi=\mu\nu^{-1}$, the intertwining integral continues analytically to a half-plane strictly to the left of $\mathrm{Re}\,s=0$, with a uniform entire denominator $B$. No flatness of the family and no fixed level are assumed. It feeds the statement [`AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation`](thm.html#AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation), and thence the analytic continuation of the constant term of Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open scoped NNReal Classical

theorem AutomorphicForm.exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W),
    let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ * ν⁻¹
    let P : ℂ → ℂ := fun w' => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w')))⁻¹
    let γ : ℂ → ℂ := fun w' => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs : ℕ) : ℂ) / 2))
    let c : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹
    ∃ (δ : ℝ) (R : ℂ → adelicMaximalCompact K → ℂ), 0 < δ ∧
      (∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -δ < s.re}) ∧
      ContinuousOn (fun p : ℂ × adelicMaximalCompact K => R p.1 p.2) ({s : ℂ | -δ < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
        γ (2 * s) * P (2 * s) * R s k = γ (2 * s + 1) * P (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K))) ∧
      (∃ B : ℂ → ℂ, Differentiable ℂ B ∧ (∀ s : ℂ, -δ < s.re → B s ≠ 0) ∧
        ∀ k : adelicMaximalCompact K, ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ, -δ < s.re → E s = B s * R s k) := by sorry
