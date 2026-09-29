-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
-- name    : AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/5e2ac028-45f5-5261-a8aa-1e04afb7f66d
-- title:
--   Vanishing torus pairing for separated induced sections
-- statement:
--   Let $K$ be a number field, and give the adele ring $\mathbb{A}_K$ and the groups built from it their Borel measurable structures. Write $\alpha_m$ for the homomorphism from $\mathbb{A}_K^\times$ to $\mathbb{R}^\times$ obtained from the module (distributive Haar) character of $\mathbb{A}_K$ through $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha_m(x)>0$ for all $x$. Let $D$ be a measurable subset of $\mathbb{A}_K^\times$ which is a fundamental domain, for the Haar measure `idelicHaar` on $\mathbb{A}_K^\times$, for the subgroup of principal ideles (the image of $K^\times$), and let $V\neq 0,\infty$ be such that for every measurable $f:\mathbb{R}\to[0,\infty]$ one has $\int^-_D f(\|z\|)\,dz = V\int^-_{(0,\infty)} f(y)y^{-1}\,dy$, where $\|\cdot\|$ is the idele norm given by the module character. Let $\mu_P,\nu_P:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be homomorphisms of absolute value $1$ that are trivial on $K^\times$, with $\mu_P$ continuous. Let $f:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be such that for each $s$ the function $f(s,\cdot)$ satisfies $f(s,bg)=\chi_1(b_{11})\chi_2(b_{22})f(s,g)$ for all upper triangular $b$, with $\chi_1=\mu_P\,\alpha_m^{s+1/2}$ and $\chi_2=\nu_P\,\alpha_m^{-(s+1/2)}$; assume $f$ jointly continuous, holomorphic in $s$ for each $g$, and of Paley–Wiener type: for every $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|f(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$, $g\in C$. Let $\mu',\nu':\mathbb{A}_K^\times\to\mathbb{C}^\times$ be homomorphisms with $\mu'$ of absolute value $1$ and trivial on $K^\times$, let $T\in\mathbb{R}$, and let $\Phi$ be continuous and satisfy the same transformation law for the pair $(\mu'\alpha_m^{iT+1/2},\,\nu'\alpha_m^{-(iT+1/2)})$. Finally suppose there is an idele $z_0$ in the kernel of the module character with $\mu_P(z_0)\neq\mu'(z_0)$. Then the function $(y,k)\mapsto\bigl(\int_{\mathbb{R}}f(it',\mathrm{diag}(y,1)k)\,dt'\bigr)\overline{\Phi(\mathrm{diag}(y,1)k)}$ is integrable for the product of the measure $\|y\|^{-1}\,dy$ on $D$ with the Haar measure on the adelic maximal compact subgroup (those $k$ whose finite part is integral of level one and whose component at each infinite place has determinant of absolute value $1$ and acts isometrically on rows), and $$\int_D \|y\|^{-1}\int_{\mathbf{K}}\Bigl(\int_{\mathbb{R}}f(it',\mathrm{diag}(y,1)k)\,dt'\Bigr)\overline{\Phi(\mathrm{diag}(y,1)k)}\,dk\,dy = 0.$$
--
--   This is the separated case of the torus pairing between a Paley–Wiener family of induced sections and a fixed continuous induced section: after the transformation laws the integrand over $D$ is $\mu_P(y)\overline{\mu'(y)}$ times a function of $\|y\|$, and the orthogonality of distinct idele class characters on the norm-one idele classes forces the pairing to vanish. It is the companion of the matched case, and feeds the statement [`AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)

      (μP νP : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμPu : IsUnitaryChar (𝓞 K) K μP) (_hνPu : IsUnitaryChar (𝓞 K) K νP)
      (_hμPic : IsIdeleClassChar (𝓞 K) K μP) (_hνPic : IsIdeleClassChar (𝓞 K) K νP)
      (_hμPc : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP x : ℂˣ) : ℂ))
      (f : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μP αm hαm s) (etaSnd νP αm hαm s) (f s))
      (_hfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => f p.1 p.2))
      (_hfhol : ∀ g, Differentiable ℂ (fun s => f s g))
      (_hfdec : ∀ (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)

      (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ'u : IsUnitaryChar (𝓞 K) K μ') (_hμ'ic : IsIdeleClassChar (𝓞 K) K μ')
      (T : ℝ) (Φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hΦ : IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((T : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((T : ℂ) * Complex.I)) Φ)
      (_hΦc : Continuous Φ)
      (z₀ : (AdeleRing (𝓞 K) K)ˣ) (_hz₀ : z₀ ∈ NumberField.TateGlobal.normOneIdeles K) (_hne : μP z₀ ≠ μ' z₀),
    Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
            conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod
          (maximalCompactHaar K)) ∧
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
          ∫ k, (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
              conj (Φ (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) = 0 := by sorry
