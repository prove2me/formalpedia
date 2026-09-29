-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
-- name    : AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/2b5626e1-3252-5beb-b307-d3752f850f2b
-- title:
--   Measurable fundamental domain inside finitely many Siegel translates
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$, written in the formalisation as `AdelicGL2 (𝓞 K) K`. Assume $0<c$, $0<d_1$ and $d_1<d_2$, and assume that the set $W=\bigcup_{x\in T}\,\{g x : g\in \mathfrak{S}^{\mathrm{cut}}(c,u,d_1,d_2)\}$ satisfies `CoversModCentre`, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z\in\mathbb{A}_K^\times$ with $\gamma g\,z\in W$, where $\gamma$ acts through the map `globalPoints` induced by $K\to\mathbb{A}_K$ and $z$ through the central scalar embedding; here $\mathfrak{S}^{\mathrm{cut}}(c,u,d_1,d_2)$ consists of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, the height bound $c\le \|\det\|/\mathrm{rowNormSq}$, the window bound $\mathrm{topNormSq}/\mathrm{rowNormSq}-(\|\det\|/\mathrm{rowNormSq})^2\le u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Let finally $0<e_1<e_2$. The conclusion asserts the existence of reals $c',u'$ with $c'>0$, a finite set $\mathrm{tset}\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ and a measurable set $\mathcal{F}\subseteq X:=\{g:\ \mathrm{ideleNorm}_K(\det g)\in[e_1,e_2]\}$ (the idele norm being the value of the distributive Haar character of $\mathbb{A}_K$) such that $\mathcal{F}$ is a fundamental domain, in the sense of `IsFundamentalDomain`, for the left action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ on the Haar measure `adelicGLHaar` restricted to $X$, and such that $\mathcal{F}\subseteq\bigcup_{t\in\mathrm{tset}}\{g t: g\in\mathfrak{S}(c',u')\}$, where $\mathfrak{S}(c',u')$ is the integrally windowed Siegel set: finite component in `finiteIntegralGL2`, product over infinite places $v$ of the local heights raised to $v.\mathrm{mult}$ at least $c'$, and window bound $\le (u')^2$ at every infinite place.
--
--   This is the reduction-theory statement that a determinant slab in $\mathrm{GL}_2(\mathbb{A}_K)$ admits a measurable fundamental domain for $\mathrm{GL}_2(K)$ which is contained in finitely many right translates of an integrally windowed Siegel set, the centre and the determinant cut of the given covering window being absorbed into the new height and window parameters and into the enlarged finite translating set. It supplies the integration domain for the Rankin–Selberg integrals, on which the Siegel-set growth and decay estimates are available, and is used in the construction of test data for those integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ (c' u' : ℝ) (tset : Finset (AdelicGL2 (𝓞 K) K)) (𝓕 : Set (AdelicGL2 (𝓞 K) K)),
      0 < c' ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet K c' u' := by sorry
