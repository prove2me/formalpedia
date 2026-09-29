-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
-- name    : AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/120bbc18-b087-57ea-bb45-e4b0321c567a
-- title:
--   Continuity of the big-cell Bruhat sum for Re s > 1/2
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and let $\alpha : \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the homomorphism obtained from Mathlib's distributive Haar character $\mathbb{A}_F^\times \to \mathbb{R}_{\ge 0}$ of the additive group $\mathbb{A}_F$ by pushing along $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units. Assume $\alpha$ takes values in the positive reals, i.e. $(\alpha x : \mathbb{R}) > 0$ for all $x$. Let $\mu, \nu : \mathbb{A}_F^\times \to \mathbb{C}^\times$ be characters with $\lVert \mu(x)\rVert = \lVert \nu(x)\rVert = 1$ for all $x$, let $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and an induced section for the pair $(\mu \cdot \alpha^{s+1/2}, \nu \cdot \alpha^{-(s+1/2)})$, meaning that for every $b \in \mathrm{GL}_2(\mathbb{A}_F)$ whose lower-left entry vanishes and every $g$, $\varphi(bg) = \mu(b_{00})\,(\alpha b_{00})^{s+1/2}\,\nu(b_{11})\,(\alpha b_{11})^{-(s+1/2)}\,\varphi(g)$, the powers being complex powers of the positive reals $\alpha b_{00}, \alpha b_{11}$. Then the function $g \mapsto \sum_{\xi \in F}' \varphi\bigl(w\, n(\xi)\, g\bigr)$ is continuous on $\mathrm{GL}_2(\mathbb{A}_F)$, where $w$ is the image of $\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$ and $n(\xi)$ that of $\bigl(\begin{smallmatrix}1&\xi\\0&1\end{smallmatrix}\bigr)$ under $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$; the sum is Lean's `tsum`, hence equal to $0$ at any $g$ where the family is not summable.
--
--   The sum over $\xi \in F$ of $\varphi$ along the big Bruhat cell, whose terms are indexed by a transversal of the rational unipotent radical, is the main constituent of the Eisenstein series attached to an induced section, and this statement records its continuity in the region $\operatorname{Re} s > 1/2$. It is used in the analysis of the Eisenstein series of $\mathrm{GL}_2$ over $F$: the decomposition into constant term plus Whittaker sum, the rapid decay of the difference, and the analytic continuation of that difference in $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean

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

theorem AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half
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
    Continuous (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) := by sorry
