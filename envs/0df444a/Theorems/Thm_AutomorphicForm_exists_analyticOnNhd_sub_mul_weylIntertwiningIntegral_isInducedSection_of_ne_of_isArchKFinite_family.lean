-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/07346a02-9560-5919-8c46-6ab9c8d18bfc
-- title:
--   Regularised Weyl intertwining integral, distinct unitary characters
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the homomorphism obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed everywhere positive via $h\alpha$. Let $\mu,\nu\colon \mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all $x$) and trivial on the principal ideles (the image of $F^\times$), with $\mu\ne\nu$. Let $\varphi\colon\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, written $\varphi_s$, be such that for every $s$ the function $\varphi_s$ is an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\ \nu\cdot\alpha^{-(s+1/2)})$, i.e. $\varphi_s(bg)=\mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\varphi_s(g)$ for every $b$ in the adelic Borel subgroup ($b_{10}=0$) and every $g$; for every $s$ the right translates of $\varphi_s$ under the row-isometry subgroup at each infinite place span a finite-dimensional space, and $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto\varphi_s(g)$ is continuous; and $s\mapsto\varphi_s(g)$ is entire for each $g$. Then, with the adeles carrying their Borel structure, there exist $a<\tfrac12$ in $\mathbb{R}$, $s_0\in\mathbb{C}$ with $s_0\ne\tfrac12$ and $\mathrm{Re}\,s_0\le\tfrac12$, and $M_{\mathrm{reg}}\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that: $s\mapsto M_{\mathrm{reg}}(s,h)$ is analytic on a neighbourhood of $\{\mathrm{Re}\,s>a\}$ for every $h$; for $\mathrm{Re}\,s>\tfrac12$ one has $M_{\mathrm{reg}}(s,h)=(s-s_0)\,V^{-1}\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)h)\,dx$, where $w$ is the adelic Weyl element, $n(x)$ the unipotent matrix, the integral is against adelic additive Haar measure and $V$ is the (real, then complexified) Haar volume of the adelic box; $(s,h)\mapsto M_{\mathrm{reg}}(s,h)$ is continuous on $\{\mathrm{Re}\,s>a\}\times\mathrm{GL}_2(\mathbb{A}_F)$; and for every $s$ with $\mathrm{Re}\,s>a$ the function $M_{\mathrm{reg}}(s,\cdot)$ is an induced section for the swapped pair $(\nu\cdot\alpha^{-s+1/2},\ \mu\cdot\alpha^{s-1/2})$ at $-s$.
--
--   This is the constant-term half of the analytic continuation of the $\mathrm{GL}_2$ Eisenstein family: the Weyl-element intertwining integral $M(s)\varphi_s$, a priori defined only for $\mathrm{Re}\,s>\tfrac12$, continues after multiplication by a single linear factor $(s-s_0)$ to a jointly continuous family of induced sections on a half-plane reaching past $\mathrm{Re}\,s=\tfrac12$, the case $\mu\ne\nu$ of distinct unitary idele class characters. It feeds the uniform moderate-growth estimate for the regularised Bruhat–Eisenstein family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hne : μ ≠ ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    ∃ (a : ℝ) (s₀ : ℂ) (Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧ s₀ ≠ 1 / 2 ∧ s₀.re ≤ 1 / 2 ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Mreg s h = (s - s₀) * (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, a < s.re →
        IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (Mreg s)) := by sorry
