-- Prove2me | Theorems.Thm_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- name    : AutomorphicForm.isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/60d7044d-c478-5fdf-963b-62d62e9585d1
-- title:
--   Unitary twist by ‖det‖^{-σ₀/2} preserves rapid decay on Siegel sets
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1$ and $d_1<d_2$, and a finite set $T$ of elements of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$. Assume the set $\bigcup_{x\in T}\{g x : g\in \text{centreCutSiegelSet}\,\mathbb{Q}\,c\,u\,d_1\,d_2\}$ covers modulo the centre, i.e. every adelic $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idele $z$ with $\gamma g\,z\in$ that union, where the centre-cut Siegel set consists of those $g$ whose finite component lies in `finiteIntegralGL2`, whose archimedean components satisfy $c\le$ `localHeight` and `xWindowSq` $\le u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$ at every infinite place. Let $\xi$ be a homomorphism from the subgroup $Z$ of the idele class group attached to `productionPinsGeneral ℚ` into $\mathbb{C}^\times$, and $\sigma_0\in\mathbb{R}$ such that $\|\xi(x)\| = \|x\|^{\sigma_0}$ for every idele $x$ (via the identification of the idele units with the top subgroup), $\|\cdot\|$ being the idele norm given by the module of the translation action on the adeles. Let $\varphi_1$ be a continuous function on adelic $\mathrm{GL}_2$ which is cusp automorphic at `productionPinsGeneral ℚ` with character $\xi$ (membership in the $L^?_\xi$-space attached to those pins together with vanishing of the unipotent constant term along `unipotentGL2`), which is reproduced by right convolution against some factorizable test function $\alpha$ (a product of an archimedean and a finite test factor) with respect to the adelic Haar measure, and which transforms under the centre by $\varphi_1(zg)=\xi(z)\varphi_1(g)$ for all ideles $z$ and all $g$. The conclusion is that $g\mapsto \varphi_1(g)\,\|\det g\|^{-\sigma_0/2}$ is rapidly decreasing on Siegel sets: for all reals $c',u'$ with $c'>0$, every adelic $t$ and every $N\in\mathbb{N}$ there is a constant $C$ with $\|\varphi_1(gt)\,\|\det(gt)\|^{-\sigma_0/2}\|\,(1+\text{archHeight}(g_\infty))^N\le C$ for all $g$ in the integral windowed Siegel set with parameters $c',u'$ (the parameters in the conclusion being quantified independently of $c,u,d_1,d_2$).
--
--   This is the rapid-decay statement for cusp forms on Siegel sets (as in Moeglin–Waldspurger I.2), in the form needed after unitarising a cusp-automorphic function whose central character has modulus $\|\cdot\|^{\sigma_0}$: the twist by $\|\det\|^{-\sigma_0/2}$ has unitary central character, and the decay estimate is transported to it. It feeds the transport of unitary twists used in the Rankin–Selberg input to the Langlands–Tunnell argument, being cited by [`AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat`](thm.html#AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat.lean

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
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁))
    (h6 : (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g)) :
    IsRapidlyDecreasingOnSiegelSets ℚ
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ₁ g * ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-σ₀ / 2) : ℝ) : ℂ)) := by sorry
