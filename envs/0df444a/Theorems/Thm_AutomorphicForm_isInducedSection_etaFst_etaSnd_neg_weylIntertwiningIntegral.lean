-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
-- name    : AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/afa660da-0859-58fa-8135-a1ed64cea0ad
-- title:
--   Weyl intertwining integral reflects the inducing character pair
-- statement:
--   Let $F$ be a number field, $\mathbb{A} =$ `AdeleRing (𝓞 F) F`, and let $\alpha : \mathbb{A}^\times \to \mathbb{R}^\times$ be the homomorphism to units obtained from the distributive Haar character of $\mathbb{A}$ composed with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$; assume $\alpha(x) > 0$ for every $x$. Let $\mu, \nu : \mathbb{A}^\times \to \mathbb{C}^\times$ be homomorphisms, $s \in \mathbb{C}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfy the induced-section law for the pair $(\mu\,\alpha^{s+1/2},\ \nu\,\alpha^{-(s+1/2)})$, where $\alpha^{z}$ denotes $x \mapsto \alpha(x)^{z}$ as a complex power of a positive real: that is, $\varphi(bg) = \mu(t_1)\alpha(t_1)^{s+1/2}\,\nu(t_2)\alpha(t_2)^{-(s+1/2)}\varphi(g)$ for all $g$ and all $b$ in the subgroup of matrices with vanishing lower-left entry, $t_1, t_2$ being the diagonal entries of $b$ viewed as units. Then, with $\mathbb{A}$ carrying its Borel $\sigma$-algebra and $dx$ the additive Haar measure, the function $g \mapsto \int_{\mathbb{A}} \varphi(w^{-1} n(x) g)\,dx$, where $w$ is the adelic point of the Weyl element and $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, satisfies the induced-section law for the reflected pair $(\nu\,\alpha^{-s+1/2},\ \mu\,\alpha^{s-1/2})$. No integrability hypothesis on $\varphi$ is imposed.
--
--   This is the left Borel transformation law of the Weyl-element intertwining operator $M(s)$ for $\mathrm{GL}_2$ over a number field: $M(s)$ carries sections induced from $(\mu\alpha^{s+1/2}, \nu\alpha^{-(s+1/2)})$ to sections induced from the pair obtained by swapping $\mu, \nu$ and replacing $s$ by $-s$. It is used in the analytic continuation and functional-equation statements for the intertwining integral and in the Maass–Selberg computations for pseudo-Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by sorry
