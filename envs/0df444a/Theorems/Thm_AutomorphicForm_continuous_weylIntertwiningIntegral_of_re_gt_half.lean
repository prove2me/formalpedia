-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half
-- name    : AutomorphicForm.continuous_weylIntertwiningIntegral_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/48d47892-01dc-5390-afb1-ceda21405d2d
-- title:
--   Continuity of the Weyl intertwining integral for Re s > 1/2
-- statement:
--   Let $F$ be a number field, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the character of the ideles obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ of $F$ by composing with the inclusion $\mathbb{R}_{\geq 0} \to \mathbb{R}$ and passing to units, and assume $\alpha(x) > 0$ for all $x$. Let $\mu, \nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be characters which are unitary in the sense that $\lvert \mu(x)\rvert = \lvert \nu(x)\rvert = 1$ for every idele $x$, and let $s \in \mathbb{C}$ satisfy $1/2 < \operatorname{Re} s$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and a section induced from the Borel subgroup at the pair of characters $\mu \cdot \alpha^{s+1/2}$ and $\nu \cdot \alpha^{-(s+1/2)}$ (complex powers being formed from the positive reals $\alpha(x)$), meaning that for every $b$ in the subgroup of matrices with vanishing lower-left entry and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ one has $\varphi(bg) = \mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\,\varphi(g)$. Then, with $\mathbb{A}_F$ carrying its Borel $\sigma$-algebra and the additive Haar measure, the function $$g \mapsto \int_{\mathbb{A}_F} \varphi\bigl(w^{-1}\,n(x)\,g\bigr)\,dx,$$ where $w$ is the adelic point of the Weyl element and $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, is continuous on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the continuity of the standard intertwining operator $M(s)$ applied to a continuous section of the induced representation $\mathrm{Ind}_B^{\mathrm{GL}_2}(\mu\lvert\cdot\rvert^{s+1/2}, \nu\lvert\cdot\rvert^{-(s+1/2)})$, in the range of absolute convergence. It is used in the Maass–Selberg computations for inner products of pseudo-Eisenstein series over slabs in the spectral parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.continuous_weylIntertwiningIntegral_of_re_gt_half
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
    Continuous (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by sorry
