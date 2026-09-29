-- Prove2me | Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
-- name    : AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/7e435fa1-b20b-5ef2-80fb-7805b04112d8
-- title:
--   Orthonormality and swapped section law of normalised intertwined family
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$ and $\mathrm{tysK}$ an archimedean type family for $K$; write $\alpha$ for the character of $(\mathbb{A}_K)^\times$ obtained from the distributive Haar character of the adele ring, valued in $\mathbb{R}^\times$, assumed everywhere positive, and give the adeles their Borel $\sigma$-algebra. Let $\mu,\nu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be continuous characters with $|\mu|=|\nu|=1$ pointwise and trivial on the principal ideles $K^\times$. Let $n\in\mathbb{N}$ and $\varphi_j(s,\cdot)$, $j<n$, be functions on $\mathrm{GL}_2(\mathbb{A}_K)$ such that each $\varphi_j(s,\cdot)$ transforms under the adelic Borel subgroup (lower-left entry zero) by the pair of characters $\mu\,\alpha^{s+1/2}$ on the first diagonal entry and $\nu\,\alpha^{-(s+1/2)}$ on the second, is archimedean $K$-finite, is $K_f$-smooth, jointly continuous in $(s,g)$ and entire in $s$, satisfies a uniform finite-dimensional $K_w$-type bound at each infinite place $w$, is flat (its restriction to the adelic maximal compact is independent of $s$), is right invariant under $\mathrm{principalLevel}(N)$ intersected with the finite adelic subgroup, lies in the archimedean cut submodule of $\mathrm{tysK}$, and has $\int_{\mathbf{K}}\varphi_i(0,k)\overline{\varphi_j(0,k)}\,dk=\delta_{ij}$ for the Haar measure on the maximal compact. Let further, for each $j$, $O_j\subseteq\mathbb{C}$ be open and preconnected containing $\{\operatorname{Re}s=0\}$ and $\{\operatorname{Re}s>1/2\}$, and $E_j,N_j$ be functions analytic in $s$ on a neighbourhood of $O_j$ for each $g$, continuous on $O_j\times\mathrm{GL}_2(\mathbb{A}_K)$, and agreeing for $\operatorname{Re}s>1/2$ with $E_j(s,g)=\varphi_j(s,g)+\sum_{\xi\in K}\varphi_j(s,w\,u(\xi)g)$ and with $N_j(s,g)=\int_{\mathbb{A}_K}\varphi_j(s,w^{-1}u(x)g)\,dx$ respectively, $w$ the adelic Weyl element and $u(x)$ the upper unipotent. Let $t\in\mathbb{R}$ and put $U_j(g)=v^{-1}N_j(it,g)$, where $v$ is the real number $\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,K)$. Then $\int_{\mathbf{K}}U_j(k)\overline{U_k(k)}\,dk=\delta_{jk}$ for all $j,k<n$, and each $U_j$ transforms under the adelic Borel subgroup by the swapped pair $\nu\,\alpha^{-it+1/2}$, $\mu\,\alpha^{it-1/2}$, is continuous, archimedean $K$-finite, right invariant under $\mathrm{principalLevel}(N)$ intersected with the finite adelic subgroup, lies in the archimedean cut submodule of $\mathrm{tysK}$, and satisfies the uniform finite-dimensional $K_w$-type bound at every infinite place.
--
--   This is the unitarity of the Weyl intertwining operator on the line $\operatorname{Re}s=0$ in the form needed downstream: on the unitary axis the normalised continued intertwining integral carries an orthonormal flat family of sections of the induced pair $(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$ to an orthonormal family of sections of the pair with $\mu,\nu$ interchanged, preserving level, continuity, archimedean $K$-finiteness and archimedean type. It feeds the Paley–Wiener and spectral-projection estimates for the Eisenstein contribution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
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
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (OE : Fin n → Set ℂ) (EE NE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (j : Fin n),
      IsOpen (OE j) ∧ IsPreconnected (OE j) ∧ {s : ℂ | s.re = 0} ⊆ (OE j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j s g) (OE j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j s g) (OE j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE j s g = φE j s g + ∑' ξ : K, φE j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE j s) g))
      (t : ℝ),
    (∀ j k : Fin n,
      ∫ kk, (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) (kk : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE k ((t : ℂ) * Complex.I) g) (kk : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) = if j = k then 1 else 0) ∧
    (∀ j : Fin n,
      IsInducedSection (𝓞 K) K (etaFst ν αm hαm (-((t : ℂ) * Complex.I))) (etaSnd μ αm hαm (-((t : ℂ) * Complex.I)))
        (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) ∧
      Continuous (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) ∧
      IsArchKFinite K (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) (g * u) =
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) ∧
      (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) g) ∈ archCutSubmodule K tysK ∧
      (∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) =>
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)) := by sorry
