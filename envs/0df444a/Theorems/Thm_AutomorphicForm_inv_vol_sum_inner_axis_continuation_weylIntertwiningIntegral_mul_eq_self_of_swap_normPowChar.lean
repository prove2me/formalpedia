-- Prove2me | Theorems.Thm_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
-- name    : AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/93ff29f5-12be-5d67-8794-34b3c28f6763
-- title:
--   Inversion of normalised intertwining operators on the unitary axis
-- statement:
--   Let $K$ be a number field, $N\neq 0$ an ideal of $\mathcal O_K$, and $\mathrm{tysK}$ a family of archimedean types (a number of representations of the row-isometry group at each infinite place). Write $\alpha_m$ for the idelic character $x\mapsto$ the real number underlying $\mathrm{distribHaarChar}$ of $x$, assumed everywhere positive. Given continuous characters $\mu,\nu$ of the idele group that are unitary ($|\chi(x)|=1$) and trivial on principal ideles, let $\varphi_1(s)$ be a family of functions on $\mathrm{GL}_2$ of the adeles which for each $s$ transforms under the Borel subgroup by $\mathrm{etaFst}\,\mu = \mu\,\alpha_m^{s+1/2}$ on the first diagonal entry and $\mathrm{etaSnd}\,\nu = \nu\,\alpha_m^{-(s+1/2)}$ on the second, is archimedean $K$-finite with a fixed finite-dimensional span of right translates at each infinite place, $K_f$-smooth, jointly continuous in $(s,g)$, holomorphic in $s$, right invariant under $\mathrm{principalLevel}\,N$ intersected with the finite-adelic subgroup, and of type $\mathrm{tysK}$; and let $O_1\ni$ the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$ be open and preconnected, with $E_1,N_1$ analytic in $s$ on $O_1$ for each $g$, jointly continuous on $O_1\times\mathrm{GL}_2$, and equal for $\mathrm{Re}\,s>1/2$ to the Eisenstein sum $\varphi_1(s)(g)+\sum_{\xi\in K}\varphi_1(s)(w\,u(\xi)g)$ and to the Weyl intertwining integral $\int\varphi_1(s)(w^{-1}u(x)g)\,dx$ over the adeles, respectively. Let $\sigma\in\mathbb R$ and let $\bar\mu=\nu\,\|\cdot\|^{i\sigma}$, $\bar\nu=\mu\,\|\cdot\|^{-i\sigma}$ be unitary continuous characters trivial on principal ideles. Let $\varphi_{E,j}$, $j<n$, be a family with the same admissibility properties for the pair $(\bar\mu,\bar\nu)$, additionally flat (its values on the maximal compact subgroup are independent of $s$), orthonormal at $s=0$ for the Haar measure of the maximal compact, and spanning: every continuous archimedean $K$-finite section of level $N$ and type $\mathrm{tysK}$ for the parameter $it$ lies in the complex span of the $\varphi_{E,j}(it)$; let $O_{E,j}, E_{E,j}, N_{E,j}$ be analytic continuations for $\varphi_{E,j}$ satisfying the same list of conditions. Then for every $t\in\mathbb R$ and every $g$, with $v$ the real volume of $\mathrm{adelicBox}\,K$ for the adelic additive Haar measure, $$v^{-1}\sum_{j'<n}\Big(\int_{\mathbf K} v^{-1}N_1(it)(k)\,\overline{\varphi_{E,j'}(-i(t+\sigma))(k)}\,dk\Big)\,N_{E,j'}(-i(t+\sigma))(g) = \varphi_1(it)(g).$$
--
--   This is the inversion identity $v^{-1}M(-it)\circ v^{-1}M(it)=\mathrm{id}$ for the normalised $\mathrm{GL}_2$ intertwining operators on the unitary axis, written in the coordinates of a complete orthonormal level-and-type family for the swapped pair $(\nu\|\cdot\|^{i\sigma},\mu\|\cdot\|^{-i\sigma})$: the normalised intertwining image of $\varphi_1(it)$ is expanded against that family and the operators are applied a second time, returning $\varphi_1(it)$. It feeds the expression of the axis continuation of an Eisenstein series as a sum of intertwining contributions over such a family, used in the analysis of constant terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar.lean

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
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
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
      (φ₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ₁ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ₁ s))
      (_hφ₁K : ∀ s, IsArchKFinite K (φ₁ s)) (_hφ₁sm : ∀ s, IsKfSmooth K (φ₁ s))
      (_hφ₁jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ₁ p.1 p.2))
      (_hφ₁hol : ∀ g, Differentiable ℂ (fun s => φ₁ s g))
      (_hφ₁Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φ₁ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφ₁lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₁ s (g * u) = φ₁ s g)
      (_hφ₁ty : ∀ (s : ℂ), φ₁ s ∈ archCutSubmodule K tysK)
      (O₁ : Set ℂ) (E₁ N₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hE₁ :
      IsOpen O₁ ∧ IsPreconnected O₁ ∧ {s : ℂ | s.re = 0} ⊆ O₁ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O₁ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E₁ s g) O₁) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => N₁ s g) O₁) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => N₁ p.1 p.2) (O₁ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        E₁ s g = φ₁ s g + ∑' ξ : K, φ₁ s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        N₁ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ₁ s) g))
      (σ : ℝ) (μb νb : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hsw : μb = ν * NumberField.TateGlobal.normPowChar K σ ∧ νb = μ * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (_hμb : IsUnitaryChar (𝓞 K) K μb) (_hνb : IsUnitaryChar (𝓞 K) K νb)
      (_hμbic : IsIdeleClassChar (𝓞 K) K μb) (_hνbic : IsIdeleClassChar (𝓞 K) K νb)
      (_hμbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μb z : ℂˣ) : ℂ))
      (_hνbc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((νb z : ℂˣ) : ℂ))
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μb αm hαm s) (etaSnd νb αm hαm s) (φE j s))
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
      (_hφEspan : ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μb αm hαm ((t : ℂ) * Complex.I)) (etaSnd νb αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
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
      (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
    ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∑ j' : Fin n,
        (∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          NE j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g =
      φ₁ ((t : ℂ) * Complex.I) g := by sorry
