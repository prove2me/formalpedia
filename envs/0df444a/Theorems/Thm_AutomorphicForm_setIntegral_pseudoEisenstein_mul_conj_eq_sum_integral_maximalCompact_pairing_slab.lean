-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
-- name    : AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6b4bdd6a-10c0-528e-af13-4f4a2007162c
-- title:
--   Parseval identity for pseudo-Eisenstein series on a determinant slab
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the distributive Haar character of $\mathbb{A}_F$ by composing with $\mathbb{R}_{\geq 0}\to\mathbb{R}$, assumed everywhere positive ($h\alpha$). Fix reals $0<d_1<d_2$, and a set $\Phi$ of adelic $\mathrm{GL}_2$-matrices contained in the slab $\{g : \|\det g\|\in[d_1,d_2]\}$ which is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ restricted to that slab. Fix a nonzero finite $c$ realising the Iwasawa formula $\int H\,dg = c\int\!\!\int\!\!\int\!\!\int H(n(x)z(u)\,\mathrm{diag}(t,1)k)\,\|t\|^{-1}\,dk\,d^\times t\,d^\times u\,dx$ for measurable $H$ with values in $[0,\infty]$, where $n(x)$ is the upper unipotent, $z(u)$ the central scalar, $dk$ Haar measure on the adelic maximal compact subgroup, and $dx$ additive adelic Haar measure; a measurable fundamental domain $D$ for the principal ideles; and a nonzero finite $V$ with $\int_D f(\|z\|)\,d^\times z = V\int_0^\infty f(y)\,y^{-1}\,dy$. Let $\xi$ be a character of the central subgroup of the carrier data $\mathrm{productionPinsOf}$ built from $\Phi$, the principal level subgroups and the Hecke generators, which subgroup is all of $(\mathbb{A}_F)^\times$. Let $\iota$ be a finite index set and $\mu,\nu:\iota\to$ characters of $(\mathbb{A}_F)^\times$ into $\mathbb{C}^\times$, each unitary and trivial on $F^\times$, with $\mu_e$ continuous, $\mu_e\nu_e=\xi$ on the central subgroup, an involutive matching $r$ with $\mu_{r e}=\nu_e$, $\nu_{r e}=\mu_e$, and distinct indices separated by $\mu$ or $\nu$ at some norm-one idele. Let $\varphi f_e(s),\psi f_e(s)$ be families of sections induced from the Borel subgroup for the pair $(\mu_e\alpha^{s+1/2},\nu_e\alpha^{-(s+1/2)})$, jointly continuous in $(s,g)$, with $s\mapsto \varphi f_e(s)(g)$ entire, and dominated on vertical strips $|\sigma'|\le\sigma_0$ and compact sets of $g$ by bounded integrable majorants $m(t)$. Let $\varphi,\psi$ satisfy [`AutomorphicForm.IsSlabProfile`](def/AutomorphicForm_SlabProfile.html#L17): measurable, invariant under all adelic unipotents and under global Borel points, transforming by $\xi$ under central scalars, bounded on every slab $\|\det g\|\in[d_1,d_2]$ with $d_1>0$, and supported where the adelic height lies in a fixed band; assume $\varphi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\varphi f_e(\sigma'+it)(g)\,dt$ for every real $\sigma'$, and likewise for $\psi$. Then for every $\sigma>1/2$, with $E(\varphi)(g)=\varphi(g)+\sum_{\beta\in F}\varphi(w\,n(\beta)g)$ the pseudo-Eisenstein series, $$\int_\Phi E(\varphi)(g)\,\overline{E(\psi)(g)}\,dg = \frac{c\,\mathrm{vol}(B)\,V^2\log(d_2/d_1)}{16\pi}\sum_e\int_{\mathbb{R}}\Big(\int_{\mathbf{K}}\varphi f_e(\sigma+it)(k)\,\overline{\psi f_e(-\sigma+it)(k)}\,dk + \mathrm{vol}(B)^{-1}\int_{\mathbf{K}}\varphi f_e(\sigma+it)(k)\,\overline{(M\psi f_{r e}(\sigma-it))(k)}\,dk\Big)dt,$$ where $B$ is the adelic box (Minkowski fundamental domain times the integral finite adeles), $\mathrm{vol}$ is its additive adelic Haar volume, and $M f(g)=\int f(w^{-1}n(x)g)\,dx$ is the Weyl intertwining integral against additive adelic Haar measure.
--
--   This is the Parseval, or inner-product, identity for pseudo-Eisenstein series on $\mathrm{GL}_2$ over a number field, truncated to a slab of determinant norms: the global pairing of two pseudo-Eisenstein series is expressed through pairings of the inducing sections over the maximal compact subgroup, together with the contribution of the Weyl intertwining operator. It feeds the decomposition of the same pairing into a residual part and a contour integral along the critical axis, [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ι)
        (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (φf ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hφdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (_hψ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (σ : ℝ) (_hσ : (1 / 2 : ℝ) < σ),
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (AutomorphicForm.pseudoEisenstein F ψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ e, ∫ t : ℝ,
      ((∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (ψf e (-(σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F))
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          ∫ k, φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
                (ψf (r e) ((σ : ℂ) - (t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F)) := by sorry
