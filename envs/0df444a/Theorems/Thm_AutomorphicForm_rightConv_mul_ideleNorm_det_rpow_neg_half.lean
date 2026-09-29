-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_mul_ideleNorm_det_rpow_neg_half
-- name    : AutomorphicForm.rightConv_mul_ideleNorm_det_rpow_neg_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c55a7e43-ba47-541b-ae6c-b41418ff3d91
-- title:
--   Right convolution commutes with the ‖det‖-twist
-- statement:
--   Let $K$ be a number field, let $w \in \mathbb{R}$, and let $\varphi, f, f'$ be complex-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$, where `AdelicGL2 (𝓞 K) K` denotes the general linear group of $2\times 2$ matrices over the adele ring of $\mathcal{O}_K$ in $K$. Write $\|x\| =$ [`NumberField.TateGlobal.ideleNorm K x`](def/NumberField_TateGlobalZeta.html#L19) for the real number obtained from the distributive Haar character of the adele ring evaluated at an idele $x$. Assume that $f'$ is the twist of $f$ by the $(w/2)$-power of the idele norm of the determinant, i.e. $f'(g) = f(g)\cdot \|\det g\|^{w/2}$ for every $g$. Then for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$,
--   $$\big((\varphi \cdot \|\det\cdot\|^{-w/2}) * f'\big)(g) = (\varphi * f)(g)\cdot\|\det g\|^{-w/2},$$
--   where `rightConv K φ f` is the function $g \mapsto \int \varphi(gx) f(x)\,dx$, the Bochner integral against the Haar measure `AdelicHaar.adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ equipped with its Borel $\sigma$-algebra. No integrability hypothesis is imposed; the identity holds with the Bochner convention that non-integrable integrands give value $0$.
--
--   This is the elementary compatibility of convolution operators on $\mathrm{GL}_2(\mathbb{A}_K)$ with twisting by a power of the idele norm of the determinant. It is used in the transport of cut traces and cuspidality classes along such determinant twists, in [`AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab`](thm.html#AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_mul_ideleNorm_det_rpow_neg_half.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightConv_mul_ideleNorm_det_rpow_neg_half
    (K : Type) [Field K] [NumberField K] (w : ℝ)
    (φ f f' : AdelicGL2 (𝓞 K) K → ℂ)
    (hff' : ∀ g : AdelicGL2 (𝓞 K) K,
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (g : AdelicGL2 (𝓞 K) K) :
    rightConv K (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) f' g =
      rightConv K φ f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ) := by sorry
