-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
-- name    : AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/9e2cf7b9-9c6c-5c4d-b962-f0afabf62f1e
-- title:
--   Weyl intertwining integral of an induced section, Re s>1/2
-- statement:
--   Let $F$ be a number field, $\mathbb{A}=\mathbb{A}_F$ its adele ring, and let $\alpha\colon \mathbb{A}^\times\to\mathbb{R}^\times$ be the character of the idele group obtained from the module character `distribHaarChar` of $\mathbb{A}$ (valued in $\mathbb{R}_{\ge 0}$, pushed into $\mathbb{R}$ and into units). Assume $\alpha$ takes positive values, let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ be characters with $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for all $x$, let $s\in\mathbb{C}$ with $\operatorname{Re} s>1/2$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ be continuous and an induced section for the pair $(\mu\,\alpha^{s+1/2},\ \nu\,\alpha^{-(s+1/2)})$, meaning that for every $b\in\mathrm{GL}_2(\mathbb{A})$ with lower-left entry $0$ and every $g$, $\varphi(bg)=\mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\,\varphi(g)$, the complex powers being those of the positive reals $\alpha(\cdot)$. Then, with $\mathbb{A}$ given its Borel $\sigma$-algebra and additive Haar measure $dx$, the function $$(M\varphi)(g)=\int_{\mathbb{A}}\varphi\bigl(w^{-1}\,n(x)\,g\bigr)\,dx,\qquad n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},$$ with $w$ the adelic point of the Weyl element, is again an induced section, now for the pair $(\nu\,\alpha^{-s+1/2},\ \mu\,\alpha^{s-1/2})$, and is continuous on $\mathrm{GL}_2(\mathbb{A})$.
--
--   This is the basic mapping property of the Weyl intertwining operator $M(s)$ between the adelic principal series induced from the Borel subgroup, in the unnormalised parametrisation with the shift by $1/2$, together with continuity of the image. It feeds the analysis of pseudo-Eisenstein series and the Maass–Selberg computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) ∧
      Continuous (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by sorry
