-- Prove2me | Theorems.Thm_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
-- name    : AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0979d91c-dd21-5c94-88a9-f14262bee089
-- title:
--   Rapid decay of the Bruhat Eisenstein series minus its constant term
-- statement:
--   Let $F$ be a number field and $c,u$ real parameters. Write $\alpha$ for the character of the idele group $\mathbb{A}_F^\times$ with values in $\mathbb{R}^\times$ obtained from the distributive Haar character `distribHaarChar` of the adele ring by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units, and assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu\colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be characters which are unitary in the sense that $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for every $x$, let $s\in\mathbb{C}$ with $\operatorname{Re} s>1/2$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: (i) $\varphi(bg)=\eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry), where $\eta_1=\mu\cdot\alpha^{\,s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$ are formed with the complex power `cpowChar`; (ii) at each infinite place $w$ the right translates of $\varphi$ under `archRowIsometrySubgroup F w` satisfy the predicate `RightTranslatesSpanFinite`; (iii) the stabiliser of $\varphi$ for right translation by the kernel of `glArch` (the group of elements trivial at the archimedean places) is open; (iv) $\varphi$ is continuous. Put $E(g)=\varphi(g)+\sum_{\xi\in F}^{\prime}\varphi(w\,n(\xi)\,g)$, the sum being Lean's `tsum` over the global points $\xi$, with $w$ the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)$ the upper unipotent matrix with entry $\xi$. The assertion is that there is a threshold $T_0\in\mathbb{R}$ such that the function $x\mapsto E(x)-\int E(n(t)x)\,dt$, the integral being taken against the additive Haar measure of $\mathbb{A}_F$ (for the Borel $\sigma$-algebra) conditioned on the adelic box, is rapidly decreasing on the set $S$ of $g$ lying in the integrally windowed Siegel set of parameters $(c,u)$ — finite part in `finiteIntegralGL2`, archimedean height at least $c$, and $\mathrm{xWindowSq}\le u^2$ at every infinite place — with archimedean height exceeding $T_0$; rapid decrease with respect to $H(g)=\mathrm{archHeight}(g)=\prod_{w\mid\infty}(\lvert\det\rvert/\mathrm{rowNormSq})^{\,[F_w:\mathbb{R}]}$ means that for every $N\in\mathbb{N}$ there is $C\in\mathbb{R}$ with $\lVert E(g)-\mathrm{CT}(E)(g)\rVert\le C\,H(g)^{-N}$ for all $g\in S$.
--
--   This is the classical estimate that an Eisenstein series differs from its constant term along the unipotent radical by a function decaying faster than any power of the height, high up in a Siegel domain; here the Eisenstein series is written in Bruhat form, the parameter normalised so that absolute convergence corresponds to $\operatorname{Re} s>1/2$, and the constant term is the integral over the adelic box, which serves as a fundamental domain for $\mathbb{A}_F/F$ carrying a probability measure. It feeds the square-integrability of the truncated pseudo-Eisenstein series, [`AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain`](thm.html#AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean

import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel
open scoped NNReal

theorem AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
    (F : Type) [Field F] [NumberField F] (c u : ℝ) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    ∃ T₀ : ℝ, IsRapidlyDecreasingOn
      (integralWindowedSiegelSet F c u ∩ {x | T₀ < archHeight F (glArch (𝓞 F) F x)})
      (fun g => archHeight F (glArch (𝓞 F) F g))
      (fun x => E x - @AutomorphicForm.constantTerm _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F)
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) E x) := by sorry
