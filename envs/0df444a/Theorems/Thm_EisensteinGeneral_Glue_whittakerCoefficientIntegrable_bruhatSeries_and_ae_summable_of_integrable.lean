-- Prove2me | Theorems.Thm_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
-- name    : EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/b18571d0-ec60-5530-aa6a-f569446cdb31
-- title:
--   Whittaker integrability and almost-everywhere summability of Bruhat series
-- statement:
--   Let $F$ be a number field, $\psi$ a continuous additive character of the adele ring $\mathbb{A}_F$ with values in $\mathbb{C}$ all of norm $1$, and $\varphi$ a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$ which is an induced section for some pair of characters: there are homomorphisms $\chi_1,\chi_2 : \mathbb{A}_F^\times \to \mathbb{C}^\times$ such that $\varphi(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (the matrices with vanishing lower-left entry). Fix $\xi \in F$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$, and assume that $y \mapsto \varphi(w\,n(y)\,g)$ is integrable on $\mathbb{A}_F$ for the additive Haar measure `adelicAddHaar`, where $w$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the Weyl element of $\mathrm{GL}_2(F)$ and $n(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$. Then two things hold. First, writing $\Phi(g') = \varphi(g') + \sum_{\xi' \in F} \varphi(w\,n(\xi')\,g')$ (the sum being the unconditional sum, $0$ when not summable), the function $x \mapsto \Phi(n(x)g)\,\psi(-\xi x)$ is integrable with respect to the measure $\nu$ of `productionPins F`, namely the adelic additive Haar measure conditioned on the set `adelicBox F`. Secondly, for $\nu$-almost every $x \in \mathbb{A}_F$ the family $\xi' \mapsto \varphi(w\,n(\xi')\,n(x)\,g)$, indexed by $F$, is summable.
--
--   This is the analytic input for the Fourier–Whittaker expansion of an adelic Eisenstein series on $\mathrm{GL}_2$: integrability of the unipotent orbit of an induced section along the Weyl translate yields both the integrability of the $\xi$-th Whittaker integrand of the Bruhat series and the pointwise convergence of that series almost everywhere. It is used by [`EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum`](thm.html#EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum), where the Whittaker coefficient of the Bruhat series is evaluated term by term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
set_option autoImplicit false

theorem EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
    (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    WhittakerCoefficientIntegrable F (productionPins F) ψ
        (fun g' => φ g' + ∑' ξ' : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g ∧
      (letI := (productionPins F).nS
        ∀ᵐ x ∂(productionPins F).ν, Summable (fun ξ' : F =>
          φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))) := by sorry
