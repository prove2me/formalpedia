-- Prove2me | Theorems.Thm_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- name    : AutomorphicForm.exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/73968b26-4264-5560-abea-cbf0b3f35ad0
-- title:
--   Boundedness of the unitarised finite Whittaker factor over ℚ
-- statement:
--   Fix real numbers $c,u,d_1,d_2$ with $0<c$, $0<d_1$ and $d_1<d_2$, and a finite set $T$ of elements of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and assume the union $\bigcup_{x\in T}(\cdot\,x)[\,S\,]$ of the right translates by $x\in T$ of the centre-cut Siegel set $S$ with parameters $c,u,d_1,d_2$ (those $g$ whose finite part is integral, whose archimedean local heights are $\ge c$, whose window coordinates satisfy $x$-window$^2\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$) covers $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ modulo the rational points and the centre. Let $\xi$ be a character of the centre subgroup $Z$ of the general production pins of $\mathbb{Q}$ with values in $\mathbb{C}^\times$, and $\sigma_0\in\mathbb{R}$ such that $|\xi(z)|=\|z\|^{\sigma_0}$ for every idele $z$, the idele norm being the module of the distributive Haar character. Let $\varphi_1:\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous, cusp-automorphic at the general production pins with character $\xi$, equal to its own right convolution (against adelic Haar measure) with some factorizable test function, and satisfying $\varphi_1(z g)=\xi(z)\varphi_1(g)$ for central scalars $z$. Suppose that the $\psi_\mathbb{Q}$-Whittaker coefficient of $\varphi_1$ at $\alpha=1$ factors as $g\mapsto W_{A,0}(\mathrm{ratArchGL2}\,g)\,W_{f,1}(\mathrm{finFactor}\,g)$, where $W_{A,0}:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ is not identically zero and $W_{f,1}$ is a function on the kernel of the archimedean projection. Then there is $B_1\in\mathbb{R}$ with $\bigl|W_{f,1}(x)\,\|\det x\|^{-\sigma_0/2}\bigr|\le B_1$ for all $x$ in that kernel.
--
--   This is the boundedness of the unitarised finite Whittaker factor of a cusp-automorphic function on $\mathrm{GL}_2$ over $\mathbb{Q}$ whose Whittaker function is a pure tensor: after twisting by $\|\det\|^{-\sigma_0/2}$ to make the central character unitary, the finite component is a bounded function. It is used in the transport of the unitary twist to shaped raw vectors, in [`AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat`](thm.html#AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.exists_bound_finWhittaker_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁))
    (h6 : (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g))
    (h9 : (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (finFactor g))) :
    ∃ B₁ : ℝ, ∀ x : finiteAdelicGL2Subgroup ℚ,
      ‖Wf₁ x * ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (-σ₀ / 2) : ℝ) : ℂ)‖ ≤ B₁ := by sorry
