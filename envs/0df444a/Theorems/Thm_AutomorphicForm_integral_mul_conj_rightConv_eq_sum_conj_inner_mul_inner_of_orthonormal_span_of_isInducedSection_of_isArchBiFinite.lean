-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
-- name    : AutomorphicForm.integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c3885344-8cbc-5a6d-83dc-ae733380478d
-- title:
--   Matrix expansion of the right-convolution pairing over K
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$ and $\mathrm{tysK}$ an archimedean type family for $K$ (a cardinality $\mathrm{card}\,w$ and representations $\mathrm{rep}\,w\,i$ of the row-isometry group at each infinite place $w$). Write $\alpha$ for the module character of the adele ring, the composite of `distribHaarChar` with $\mathbb{R}_{\ge0}\to\mathbb{R}$ viewed as a homomorphism to $\mathbb{R}^\times$, assumed everywhere positive, and for $s\in\mathbb{C}$ put $\eta_1(s)=\mu\cdot\alpha^{s+1/2}$, $\eta_2(s)=\nu\cdot\alpha^{-(s+1/2)}$, where $\mu,\nu$ are idele class characters of absolute value $1$ at every idele. Let $\varphi_0,\dots,\varphi_{n-1}$ be functions of $s$ and of $g\in \mathrm{GL}_2(\mathbb{A}_K)$ such that each $\varphi_j(s)$ is continuous and satisfies $\varphi_j(s)(bg)=\eta_1(s)(b_{11})\,\eta_2(s)(b_{22})\,\varphi_j(s)(g)$ for all $b$ in the adelic Borel subgroup (lower-left entry zero), such that $\varphi_j(s)$ and $\varphi_j(0)$ agree on the maximal compact subgroup $\mathbf{K}$ (the matrices integral at all finite places and row-isometric at all infinite places), and such that $\int_{\mathbf{K}}\varphi_i(0)\overline{\varphi_j(0)}\,dk=\delta_{ij}$ for the Haar measure `maximalCompactHaar`. Fix $t\in\mathbb{R}$ and set $s_0=it$. Assume the completeness hypothesis: every continuous $\varphi_0'$ satisfying the same induced-section identity at $s_0$, archimedean $K$-finite at every infinite place, right invariant under $\mathrm{principalLevel}(N)$ intersected with the kernel of the archimedean projection, and lying in the archimedean cut submodule attached to $\mathrm{tysK}$, lies in the $\mathbb{C}$-span of the $\varphi_j(s_0)$. Let $f$ be continuous with compact support, factorizable as a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor, bi-invariant under the same level group, and archimedean bi-finite of types $\mathrm{tysK}$ (that is, $g\mapsto f(g^{-1})$ lies in the cut submodule and $f$ in the dual cut submodule). Finally let $\Phi$ be any continuous function and $\Psi$ any continuous induced section at $s_0$. Then, with $R(f)\varphi(g)=\int \varphi(gx)f(x)\,dx$ for the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ and $\langle a,b\rangle=\int_{\mathbf{K}}a\overline{b}\,dk$, $$\langle \Phi, R(f)\Psi\rangle=\sum_{i,j<n}\overline{\langle R(f)\varphi_j(s_0),\varphi_i(s_0)\rangle}\;\langle\Phi,\varphi_i(s_0)\rangle\;\overline{\langle\Psi,\varphi_j(s_0)\rangle}.$$
--
--   This expresses the right-convolution operator $R(f)$ on the line $s=it$ of the induced family as $P_VR(f)P_V$ for $V$ the span of the orthonormal family $\varphi_\bullet(it)$, turning the pairing $\langle\Phi,R(f)\Psi\rangle$ over the maximal compact subgroup into a finite bilinear expression in the matrix coefficients of $R(f)$ on $V$. Unlike the variant in which $\Psi$ is itself constrained, here $\Phi$ and $\Psi$ carry no level, type or finiteness condition; it is used by [`AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched`](thm.html#AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched) in the spectral side of the trace computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite.lean

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

theorem AutomorphicForm.integral_mul_conj_rightConv_eq_sum_conj_inner_mul_inner_of_orthonormal_span_of_isInducedSection_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (n : ℕ) (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφEc : ∀ j s, Continuous (φE j s))
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (t : ℝ)
      (_hφEspan : ∀ (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hfF : IsFactorizableTestFn K f)
      (_hfbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
      (_hfty : IsArchBiFinite K tysK f)
      (Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΦc : Continuous Φ)
      (_hΨ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) Ψ)
      (_hΨc : Continuous Ψ),
    ∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∑ i : Fin n, ∑ j : Fin n,
        conj (∫ k, rightConv K (φE j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
        ((∫ k, Φ (k : AdelicGL2 (𝓞 K) K) * conj (φE i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          conj (∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by sorry
