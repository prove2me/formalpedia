-- Prove2me | Theorems.Thm_AddChar_exists_continuousLinearMap_fourierChar_eq
-- name    : AddChar.exists_continuousLinearMap_fourierChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/141e021a-e939-522a-8662-8e39e4ff29ab
-- title:
--   Continuous circle characters of a real normed space
-- statement:
--   Let $E$ be a real normed vector space (a normed additive commutative group with a compatible $\mathbb{R}$-vector space structure), and let $\chi$ be an additive character of $E$ with values in the circle group, that is, a map $\chi\colon E\to S^1\subset\mathbb{C}^\times$ with $\chi(0)=1$ and $\chi(x+y)=\chi(x)\chi(y)$ for all $x,y\in E$. Assume $\chi$ is continuous. The assertion is that there exists a continuous $\mathbb{R}$-linear functional $l\colon E\to\mathbb{R}$, an element of $E \to_{L[\mathbb{R}]} \mathbb{R}$, such that for every $x\in E$ one has $\chi(x)=\mathbf{e}(l(x))$, where $\mathbf{e}$ denotes `Real.fourierChar`, the character $t\mapsto e^{2\pi i t}$ of $\mathbb{R}$ with values in the circle group; the equality is an equality of elements of $S^1$. No completeness, separability or finite-dimensionality hypothesis is imposed on $E$, and no uniqueness of $l$ is asserted (though $l$ is in fact determined by $\chi$).
--
--   This is the classification of the continuous unitary characters of the additive group of a real normed space: composition with $t\mapsto e^{2\pi i t}$ identifies the topological dual of $E$ with its Pontryagin dual. It is used in the analysis of characters on completions at infinite places and on the adeles of a number field, in particular by [`NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar`](thm.html#NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar) and [`NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous`](thm.html#NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddChar_exists_continuousLinearMap_fourierChar_eq.lean

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform

theorem AddChar.exists_continuousLinearMap_fourierChar_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by sorry
