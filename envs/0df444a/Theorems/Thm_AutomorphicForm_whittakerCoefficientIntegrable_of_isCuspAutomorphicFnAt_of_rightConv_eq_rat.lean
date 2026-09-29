-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat
-- name    : AutomorphicForm.whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/229fcb06-086d-5bf1-8a1b-336f2e3244b1
-- title:
--   Integrable Whittaker slices for reproduced cusp forms over ℚ
-- statement:
--   Work over $F=\mathbb{Q}$ with the pins package `productionPinsGeneral ℚ`, i.e. the production data attached to the parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$: fundamental-domain set the class-representative Siegel set `classRepSiegelSet ℚ (1/2) 1 (1/2) 2`, level subgroups $N\mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, Hecke generators `heckeGen`, and the measurable space and measure $\nu$ on $\mathbb{A}_{\mathbb{Q}}$ coming from `adelicBox ℚ`. Let $\xi$ be a group homomorphism from the central subgroup `(productionPinsGeneral ℚ).Z` of $\mathbb{A}_{\mathbb{Q}}^{\times}$ to $\mathbb{C}^{\times}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, cusp-automorphic at these pins with character $\xi$, meaning $\varphi$ satisfies `LsXiMemberAt` for the pins' measure, domain and central data, and its constant term $\int \varphi(n(x)g)\,d\nu(x)$ along the unipotent $x\mapsto$ `unipotentGL2 x` vanishes for every $g$. Assume further that $\varphi$ is reproduced by right convolution against some factorizable test function $\alpha$: $\alpha$ is a product of an archimedean factor which is compactly supported and arises from a $C^\infty$ function on matrices over the mixed space via `archEntries`, and of a locally constant compactly supported factor on $\mathrm{GL}_2$ of the finite adeles, and $g\mapsto\int \varphi(gx)\alpha(x)\,dx$ (Haar measure on the adelic $\mathrm{GL}_2$) equals $\varphi$. Then for every $a\in\mathbb{Q}$ and every $g\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ the function $x\mapsto \varphi(n(x)g)\,\psi_{\mathbb{Q}}(-(a x))$, with $\psi_{\mathbb{Q}}=$ [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) the standard global additive character and $a$ pushed into $\mathbb{A}_{\mathbb{Q}}$, is integrable with respect to $\nu$.
--
--   This is the integrability half of the Fourier–Whittaker expansion of an adelic cusp form over $\mathbb{Q}$: it licenses writing down Whittaker coefficients $W_a(g)$ of $\varphi$ along the standard unipotent. It is used repeatedly in the shaping of Rankin–Selberg test data, by [`AutomorphicForm.isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat`](thm.html#AutomorphicForm.isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat), [`AutomorphicForm.shapedRaw_rawBundle_transl_rat`](thm.html#AutomorphicForm.shapedRaw_rawBundle_transl_rat) and [`AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat`](thm.html#AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat), each of which needs slice integrability at every step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

theorem AutomorphicForm.whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous φ)
    (hφ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ)
    (hrep : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g := by sorry
