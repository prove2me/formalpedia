-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
-- name    : AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9cff11c4-60a7-54dd-b73e-8c50c07b0390
-- title:
--   Torus pairing of a matched Paley–Wiener packet by Mellin inversion
-- statement:
--   Let $K$ be a number field, and let $\alpha_m$ be the homomorphism from the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{R}^\times$ obtained from the module character `distribHaarChar` of the adele ring composed with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$, the adele ring carrying its Borel measurable structure; assume $\alpha_m$ takes positive values. Let $D$ be a measurable subset of $(\mathbb{A}_K)^\times$ which is a fundamental domain, for the Haar measure `idelicHaar`, for the subgroup of principal ideles (the image of $K^\times$), and let $V \in [0,\infty]$ be non-zero and finite such that for every measurable $f:\mathbb{R}\to[0,\infty]$ one has $\int^-_D f(\|z\|)\,dz = V\cdot\int^-_{(0,\infty)} f(y)\,y^{-1}$, where $\|\cdot\|$ is the idele norm `ideleNorm` (the value of the module character). Let $\mu_P,\nu_P:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be characters, each of absolute value $1$ at every idele and trivial on principal ideles, with $\mu_P$ continuous. Let $f:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be such that for each $s$ the function $f(s,\cdot)$ satisfies $f(s, bg) = \chi_1(b_{11})\chi_2(b_{22})f(s,g)$ for all $g$ and all $b$ with vanishing lower-left entry, where $\chi_1 = \mu_P\cdot\alpha_m^{\,s+1/2}$ and $\chi_2 = \nu_P\cdot\alpha_m^{-(s+1/2)}$; assume $f$ jointly continuous, holomorphic in $s$ for each $g$, and of rapid decay on vertical strips in the sense that for every $n\in\mathbb{N}$, every $\sigma_0$ and every compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\,\|f(\sigma'+it, g)\| \le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Let $\mu',\nu'$ be further characters with $\mu'$ of absolute value $1$ and trivial on principal ideles, let $T\in\mathbb{R}$, and let $\Phi$ be continuous and satisfy the same transformation law with respect to $\mu'\cdot\alpha_m^{\,iT+1/2}$ and $\nu'\cdot\alpha_m^{-(iT+1/2)}$. Assume the matching $\mu_P = \mu'\cdot\|\cdot\|^{\,i\tau_0}$ for some $\tau_0\in\mathbb{R}$. Then the function $(y,k)\mapsto \bigl(\int_{\mathbb{R}} f(it',\mathrm{diag}(y,1)k)\,dt'\bigr)\,\overline{\Phi(\mathrm{diag}(y,1)k)}$ is integrable for the product of `idelicHaar` restricted to $D$ and weighted by the density $\|y\|^{-1}$ with the Haar measure of the compact subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of elements whose finite part is integral of full level and whose component at each infinite place is a row isometry, and $$\int_D \|y\|^{-1}\int_{\mathbf K}\Bigl(\int_{\mathbb{R}} f(it',\mathrm{diag}(y,1)k)\,dt'\Bigr)\overline{\Phi(\mathrm{diag}(y,1)k)}\,dk\,dy = 2\pi V\int_{\mathbf K} f\bigl(i(T-\tau_0),k\bigr)\overline{\Phi(k)}\,dk,$$ with $V$ read as a real number.
--
--   This is the evaluation of the torus pairing of a Paley–Wiener packet of induced sections against a single induced section whose first character matches up to a norm twist: the transformation law on the diagonal torus reduces the integral over the fundamental domain to a $dy/y$-integral through the norm push-forward, and Fourier inversion in $\log\|y\|$ picks out the member at $i(T-\tau_0)$. It feeds the constant-term pairing statement [`AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener) in the spectral analysis of pseudo-Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar.lean

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

theorem AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
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
      (τ₀ : ℝ) (_hmatch : μP = μ' * NumberField.TateGlobal.normPowChar K τ₀),
    Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
            conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod
          (maximalCompactHaar K)) ∧
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
          ∫ k, (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
              conj (Φ (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) =
      ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) *
        ∫ k, f (((T - τ₀ : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (Φ (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K) := by sorry
