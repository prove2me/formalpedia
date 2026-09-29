-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/73c83021-47f1-5bdf-adb2-46511e985245
-- title:
--   Regularised Weyl intertwining integral continues past Re s=1/2
-- statement:
--   Let $F$ be a number field, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the monoid homomorphism obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ of $F$ by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units; assume $\alpha(t) > 0$ for all $t$. Let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for each $s$, $\varphi_s$ is an induced section for the pair of characters $(\alpha^{s+1/2}, \alpha^{-(s+1/2)})$, i.e. $\varphi_s(bg) = \alpha(b_{00})^{s+1/2}\,\alpha(b_{11})^{-(s+1/2)}\varphi_s(g)$ for every $g$ and every invertible $b$ with $b_{10} = 0$ (the complex powers being those of the positive reals $\alpha(b_{ii})$); for each $s$ and each infinite place $w$ of $F$, the right translates of $\varphi_s$ by the row-isometry subgroup at $w$ span a finite-dimensional space; each $\varphi_s$ is a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto \varphi_s(g)$ is jointly continuous; and $s \mapsto \varphi_s(g)$ is entire for each $g$. Then, with the Borel $\sigma$-algebra on $\mathbb{A}_F$, there are a real number $a < 1/2$ and $M_{\mathrm{reg}} : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ such that: $s \mapsto M_{\mathrm{reg}}(s,h)$ is analytic on a neighbourhood of every point of $\{\operatorname{Re} s > a\}$, for each $h$; for $\operatorname{Re} s > 1/2$ one has $M_{\mathrm{reg}}(s,h) = (s-\tfrac12)\,\mathrm{vol}^{-1}\int_{\mathbb{A}_F} \varphi_s(w^{-1} n(x) h)\,dx$, where $w$ is the adelic Weyl element, $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, the integral is against the adelic additive Haar measure and $\mathrm{vol}$ is the measure of the adelic box; $(s,h) \mapsto M_{\mathrm{reg}}(s,h)$ is continuous on $\{\operatorname{Re} s > a\} \times \mathrm{GL}_2(\mathbb{A}_F)$; and for every $s$ with $\operatorname{Re} s > a$, $M_{\mathrm{reg}}(s,\cdot)$ is an induced section for the pair $(\alpha^{1/2-s}, \alpha^{s-1/2})$.
--
--   This is the analytic continuation, with a simple pole at $s = 1/2$ removed, of the Weyl-element intertwining operator $M(s)$ on the degenerate principal series of $\mathrm{GL}_2(\mathbb{A}_F)$ induced from $(\alpha^{s+1/2}, \alpha^{-(s+1/2)})$, together with the statement that the regularised operator remains jointly continuous and takes values in the sections induced from the reflected pair. It feeds the uniform moderate-growth bounds for the constant term of the regularised spherical Eisenstein family and the computation of the residue of the intertwining operator at $s = 1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    ∃ (a : ℝ) (Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Mreg s h = (s - 1 / 2) * (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, a < s.re →
        IsInducedSection (𝓞 F) F (etaFst 1 α hα (-s)) (etaSnd 1 α hα (-s)) (Mreg s)) := by sorry
