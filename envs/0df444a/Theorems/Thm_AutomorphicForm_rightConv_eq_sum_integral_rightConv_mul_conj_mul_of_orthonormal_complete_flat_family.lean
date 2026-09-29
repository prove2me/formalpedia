-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family
-- name    : AutomorphicForm.rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a562e84f-cd20-5e26-9f67-2f6a6c5f187a
-- title:
--   Convolution of a flat section expands in the orthonormal family
-- statement:
--   Let $K$ be a number field, and fix the following ambient data: reals $0<\alpha<\beta$, a set $\Phi_K$ of adelic $GL_2$ elements, constants $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$ and $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq GL_2(\mathbb{A}_K)$ such that the union of the right translates $(\cdot\,x)$ of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ over $x\in T_K$ covers $GL_2(\mathbb{A}_K)$ modulo $GL_2(K)$ and the adelic centre; a Haar measure $\nu_{Z_K}$ on the idele group together with a set $\Omega_K$ that is a fundamental domain for the image of $K^\times$; a finite set $S_K$ of finite places containing every $v$ with $v \mid N$, where $N$ is an ideal of $\mathcal{O}_K$; a continuous unitary character $\xi_K$ of the full idele group, trivial on the image of $K^\times$; and a family $\mathrm{tys}_K$ assigning to each infinite place finitely many representations of the row-isometry group of the completion. Write $\alpha_m$ for the character $\mathbb{A}_K^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character, assumed everywhere positive. Let $\iota_E$ be a countable index type and $\mu,\nu : \iota_E \to \mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ families of continuous characters, each of absolute value $1$ and trivial on $K^\times$, with $\mu_e \nu_e = \xi_K$ for every $e$, and with distinct indices separated by some norm-one idele. For each $e$ let $\varphi_{e,j}(s,\cdot)$, $j \in \mathrm{Fin}(n_E\,e)$, be functions on $GL_2(\mathbb{A}_K)$ such that: each $\varphi_{e,j}(s,\cdot)$ transforms under the adelic Borel by the characters $\mu_e\,\alpha_m^{\,s+1/2}$ and $\nu_e\,\alpha_m^{-(s+1/2)}$ on the two diagonal entries; each is archimedean $K$-finite, smooth for the finite-adelic subgroup, jointly continuous in $(s,g)$, entire in $s$ for fixed $g$, archimedean $K$-finite uniformly in $s$ (translates lying in one fixed finite-dimensional space per infinite place), right invariant under $\mathrm{principalLevel}(N)$ intersected with the finite-adelic subgroup, and contained in the archimedean cut submodule of type $\mathrm{tys}_K$; the family is flat, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in the adelic maximal compact; it is orthonormal at $s=0$ against the Haar measure of the maximal compact; and it is complete, in the sense that on the imaginary axis every nonzero continuous archimedean $K$-finite induced section of the same type, invariant under the level group, lies in the span of the $\varphi_{e,j}$, while every admissible pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ carrying such a section agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Assume further given, for each $e,j$, an open preconnected set $O_{e,j}\subseteq\mathbb{C}$ containing the imaginary axis and the half-plane $\operatorname{Re} s > 1/2$, and functions $E_{e,j}, N_{e,j}$ analytic in $s$ on $O_{e,j}$ for each $g$ and continuous on $O_{e,j} \times GL_2(\mathbb{A}_K)$, which for $\operatorname{Re} s > 1/2$ are given by the Bruhat expansion $E_{e,j}(s,g) = \varphi_{e,j}(s,g) + \sum_{\xi \in K}\varphi_{e,j}(s, w\,u(\xi)\,g)$ and by the Weyl intertwining integral $N_{e,j}(s,g) = \int_{\mathbb{A}_K}\varphi_{e,j}(s, w^{-1}u(x)g)\,dx$. Finally let $f$ be a continuous, compactly supported test function that is factorizable (a product of a compactly supported smooth archimedean factor and a locally constant compactly supported finite factor), bi-invariant under $\mathrm{principalLevel}(N)$ intersected with the finite-adelic subgroup, and archimedean bi-finite of type $\mathrm{tys}_K$. The conclusion is that for every $e$, every $j$, every $s \in \mathbb{C}$ and every $g \in GL_2(\mathbb{A}_K)$, the right convolution $(\mathrm{rightConv}\,K\,\varphi_{e,j}(s,\cdot)\,f)(g) = \int \varphi_{e,j}(s, gx) f(x)\,dx$ equals $\sum_i \bigl(\int_{\mathbf{K}} (\mathrm{rightConv}\,K\,\varphi_{e,j}(s,\cdot)\,f)(k)\,\overline{\varphi_{e,i}(s,k)}\,dk\bigr)\,\varphi_{e,i}(s,g)$, the integrals over the maximal compact being taken against its Haar measure. Note that the expansion is asserted for all complex $s$, not only on the imaginary axis where completeness is assumed.
--
--   This is the section-level half of the $R(f)$-equivariance of degenerate principal series in the adelic Eisenstein construction: right convolution by a factorizable bi-invariant test function preserves the finite-dimensional space cut out by the level, the archimedean types and the inducing characters, so it is reproduced by its inner products against the chosen orthonormal flat family. It feeds the corresponding statement for the analytic continuation of the Weyl intertwining integral, where the identity is propagated from $\operatorname{Re} s > 1/2$ to the continuation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (e : ιE) (j : Fin (nE e)) (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      rightConv K (φE e j s) f g =
      ∑ i : Fin (nE e),
        (∫ k, rightConv K (φE e j s) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i s (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
          φE e i s g := by sorry
