-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
-- name    : AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/731f7d45-d282-5cf1-b8b3-05424d11db34
-- title:
--   Continuity of right convolution on adelic GL₂
-- statement:
--   Let $F$ be a number field, and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for the general linear group of $2\times 2$ matrices over the adele ring of $F$, equipped with its Borel $\sigma$-algebra and with the Haar measure `adelicGLHaar` on it. Let $\varphi : G \to \mathbb{C}$ be continuous, and let $g : G \to \mathbb{C}$ be continuous with compact support (that is, the closure of $\{y : g(y) \neq 0\}$ is compact). The conclusion is that the function [`AutomorphicForm.rightConv F φ g`](def/AutomorphicForm_RightConvolution.html#L9), defined by
--   $$x \mapsto \int_{G} \varphi(xy)\,g(y)\,d y$$
--   with respect to that Haar measure, is continuous on $G$. Here the integral is the Bochner integral of the $\mathbb{C}$-valued function $y \mapsto \varphi(xy)g(y)$; no invariance, growth or automorphy hypothesis is imposed on $\varphi$, and no normalisation of $g$ beyond continuity and compact support.
--
--   This is the standard fact that convolution of an arbitrary continuous function with a continuous compactly supported kernel on a locally compact group produces a continuous function. It is used in the spectral theory of $\mathrm{GL}_2$ automorphic forms, where right convolution by such kernels acts as a smoothing operator and continuity of the output is part of checking that the operator maps spaces of automorphic forms to themselves; it is cited by the results on cuspidal constituents and isotypic cusp submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

theorem AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (AutomorphicForm.rightConv F φ g) := by sorry
