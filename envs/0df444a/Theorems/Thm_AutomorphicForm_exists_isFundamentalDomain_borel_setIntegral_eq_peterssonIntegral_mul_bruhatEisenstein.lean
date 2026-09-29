-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
-- name    : AutomorphicForm.exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/5bd89e99-3a3c-5001-aaf4-0fb8de6281a6
-- title:
--   Eisenstein unfolding to a rational Borel fundamental domain
-- statement:
--   Let $F$ be a number field and let $\alpha\colon\mathbb A_F^\times\to\mathbb R^\times$ be the unit-valued homomorphism obtained from the distributive Haar character of $\mathbb A_F$ via $\mathbb R_{\ge 0}\to\mathbb R$, assumed everywhere positive. Fix characters $\mu,\nu\colon\mathbb A_F^\times\to\mathbb C^\times$ trivial on the principal ideles $F^\times$, a complex $s$, and $\varphi\colon\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ satisfying $\varphi(bg)=\eta_1(b_{11})\,\eta_2(b_{22})\,\varphi(g)$ for every adelic matrix $b$ with $b_{21}=0$, where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$; assume $\varphi$ continuous and, for each $g$, $\sum_{\xi\in F}\|\varphi(\omega\,n(\xi)g)\|$ summable, $\omega=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ taken in $\mathrm{GL}_2(\mathbb A_F)$. Let $x,y$ be continuous and left invariant under $\mathrm{GL}_2(F)$, let $w,d_1,d_2\in\mathbb R$ with $0<d_1<d_2$, and let $\mathcal F$ be contained in the slab $\{\,\|\det g\|\in[d_1,d_2]\,\}$ and be a fundamental domain for $\mathrm{GL}_2(F)$ acting on the adelic Haar measure restricted to that slab, with $\|x\|^2(\|\varphi\|+\sum_\xi\|\varphi(\omega n(\xi)\cdot)\|)\|\det\|^{-w}$ and its analogue for $y$ integrable on $\mathcal F$. Then there is a measurable fundamental domain $\mathcal F_B$ for the image of the rational Borel subgroup in $\mathrm{GL}_2(\mathbb A_F)$ acting on the full Haar measure such that $\mathbf 1_{\mathrm{slab}}\,x\varphi\overline y\,\|\det\|^{-w}$ is integrable on $\mathcal F_B$ with $$\int_{\mathcal F_B}\mathbf 1_{\mathrm{slab}}(g)\,x(g)\varphi(g)\overline{y(g)}\,\|\det g\|^{-w}\,dg=\int_{\mathcal F}x(g)\Big(\varphi(g)+\sum_{\xi\in F}\varphi(\omega n(\xi)g)\Big)\overline{y(g)}\,\|\det g\|^{-w}\,dg,$$ and such that the upper integrals over $\mathcal F_B$ of $\mathbf 1_{\mathrm{slab}}\|x\|^2\|\varphi\|\|\det\|^{-w}$ and of $\mathbf 1_{\mathrm{slab}}\|y\|^2\|\varphi\|\|\det\|^{-w}$ are both finite. Here $\|\cdot\|$ is the idele norm given by the distributive Haar character, and the right-hand side is the Petersson integral of $x\cdot E$ against $y$ with exponent $-w$ over $\mathcal F$.
--
--   This is the first step of the global Rankin–Selberg unfolding for $\mathrm{GL}_2$ over a number field: the Bruhat decomposition of the Eisenstein series attached to an induced section converts an integral over a fundamental domain for $\mathrm{GL}_2(F)$ into one over a fundamental domain for the rational Borel subgroup, with the determinant slab carried along as an indicator. It feeds the subsequent passage to Whittaker coefficients over the rational centre–unipotent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hintx : IntegrableOn (fun g => ‖x g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hinty : IntegrableOn (fun g => ‖y g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)),
    ∃ 𝓕B : Set (AdelicGL2 (𝓞 F) F), MeasurableSet 𝓕B ∧
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ g in 𝓕B,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        peterssonIntegral F w 𝓕
          (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖x g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖y g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by sorry
