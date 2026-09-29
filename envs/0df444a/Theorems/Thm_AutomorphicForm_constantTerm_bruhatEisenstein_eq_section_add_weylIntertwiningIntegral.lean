-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
-- name    : AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/65234669-bc7c-5446-96c4-7e0d6dc3352b
-- title:
--   Constant term of the Bruhat Eisenstein series for Re s>1/2
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from Mathlib's distributive Haar character of the adele ring by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units; assume $\alpha$ takes strictly positive real values. Let $\mu,\nu$ be characters $(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ which are unitary in the sense that $\|\mu(x)\|=\|\nu(x)\|=1$ for every idele $x$, let $s\in\mathbb{C}$ with $\mathrm{Re}\,s>1/2$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\ \nu\cdot\alpha^{-(s+1/2)})$, i.e. $\varphi(bg)=\eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$ for all $g$ and all $b$ in the Borel subgroup of matrices with vanishing lower-left entry, where $\eta_1,\eta_2$ are those two characters and $b_{00},b_{11}$ are the diagonal entries of $b$ viewed as ideles. Fix $g\in\mathrm{GL}_2(\mathbb{A}_F)$, and set $E(g')=\varphi(g')+\sum'_{\xi\in F}\varphi(w\,n(\xi)\,g')$, where $w$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the Weyl element of $\mathrm{GL}_2(F)$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then the constant term of $E$ at $g$ along the unipotent family $n$, formed by integrating the associated integrand against the conditioning of adelic additive Haar measure (for the Borel $\sigma$-algebra on $\mathbb{A}_F$) on the adelic box $\{x:\ x_\infty\in\text{infiniteBox}\ F,\ x_{\mathrm{fin}}\ \text{integral}\}$, equals $\varphi(g)+\mathrm{vol}(\text{adelicBox}\ F)^{-1}\int_{\mathbb{A}_F}\varphi(w^{-1}n(x)g)\,dx$, the volume being the real number attached to the Haar measure of the box and the integral being `weylIntertwiningIntegral` for adelic Haar measure.
--
--   This is the classical unfolding of the constant term of a $\mathrm{GL}(2)$ Eisenstein series over a number field in the region of absolute convergence: the two Bruhat cells contribute the section itself and the Weyl intertwining integral $M(s)\varphi$, up to the normalising volume of the box used to form the conditioned measure. It feeds the statements on analytic continuation of the constant term and on the decay of the Eisenstein series minus its constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by sorry
