-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family_light
-- name    : AutomorphicForm.rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family_light
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/7f713a88-0be6-52e0-94b5-772336709736
-- title:
--   Expansion of R(f)φ_{e,j,s} in a flat orthonormal family
-- statement:
--   Let $K$ be a number field, $0<\alpha<\beta$ reals, $S_K$ a finite set of finite places, and $\xi_K$ a continuous homomorphism from the full idele unit group to $\mathbb{C}^\times$ that is trivial on the principal ideles and of absolute value $1$; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, and $\mathrm{tys}_K$ a family assigning to each infinite place finitely many finite-dimensional representations of the row-isometry group. Write $\alpha_m$ for the character of the ideles obtained from the module function $\mathrm{distribHaarChar}$ of the adele ring, assumed everywhere positive. Let $\iota_E$ be countable, and $\mu,\nu:\iota_E\to\operatorname{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ continuous unitary characters trivial on $K^\times$ with $\mu_e\nu_e=\xi_K$, pairwise separated by some norm-one idele (an element of the kernel of $\mathrm{distribHaarChar}$). For each $e$ let $\varphi_{e,j,s}$, $j\in\mathrm{Fin}(n_E(e))$, be functions on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying: the induction rule $\varphi(bg)=\mu_e(b_{11})|b_{11}|_{\alpha_m}^{s+1/2}\,\nu_e(b_{22})|b_{22}|_{\alpha_m}^{-(s+1/2)}\varphi(g)$ for $b$ in the adelic Borel; archimedean $K$-finiteness, $K_f$-smoothness (open stabiliser in $\ker(\mathrm{glArch})$), joint continuity in $(s,g)$, holomorphy in $s$, a place-by-place finite-dimensional bound on right translates by the archimedean row-isometry subgroups, flatness ($\varphi_{e,j,s}=\varphi_{e,j,0}$ on the maximal compact), right invariance under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, membership in the type cut $\mathrm{archCutSubmodule}$, orthonormality of $(\varphi_{e,j,0})_j$ for the Haar measure on the adelic maximal compact, and completeness: every continuous archimedean $K$-finite section of the same type on the axis $s=it$, invariant under the level group and in the type cut, lies in the span of the $\varphi_{e,j,it}$. Data $O_{e,j}$, $E_{e,j}$, $N_{e,j}$ are also given, with $O_{e,j}$ open and preconnected containing the imaginary axis and $\{\operatorname{Re} s>1/2\}$, $E_{e,j}$ and $N_{e,j}$ analytic in $s$ there and continuous in $(s,g)$, agreeing for $\operatorname{Re} s>1/2$ with the Bruhat sum $\varphi_{e,j,s}(g)+\sum_{\xi\in K}\varphi_{e,j,s}(w\,u(\xi)g)$ and with the Weyl intertwining integral $\int\varphi_{e,j,s}(w^{-1}u(x)g)\,dx$ respectively. Finally let $f$ be continuous of compact support, factorizable (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor), bi-invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, and archimedean bi-finite of type $\mathrm{tys}_K$. Then for all $e$, $j$, all $s\in\mathbb{C}$ and all $g$, the right convolution $R(f)\varphi_{e,j,s}(g)=\int\varphi_{e,j,s}(gx)f(x)\,dx$ equals $\sum_i\bigl(\int_{\mathbf{K}}R(f)\varphi_{e,j,s}(k)\,\overline{\varphi_{e,i,s}(k)}\,dk\bigr)\varphi_{e,i,s}(g)$.
--
--   This is the section-level half of the $R(f)$-equivariance of adelic Eisenstein series: the convolution $R(f)\varphi_{e,j,s}$ is again a section of the same induced type, hence a finite combination of the basis $(\varphi_{e,i,s})_i$ with coefficients given by inner products over the maximal compact, and the identity is obtained for all $s$, not only on the axis, from flatness of the family. It feeds the corresponding statement for the analytic continuations of the Eisenstein and Weyl intertwining terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family_light.lean

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
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_eq_sum_integral_rightConv_mul_conj_mul_of_orthonormal_complete_flat_family_light
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
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
