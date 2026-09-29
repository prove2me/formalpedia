-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous
-- name    : AutomorphicForm.exists_eq_archWeightCharReal_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b915e599-74dd-5797-a9f0-056b0eece303
-- title:
--   Continuous characters of the real row-isometry group are integral
-- statement:
--   Let $\chi$ be a group homomorphism from the group `rowIsometrySubgroup₀ ℝ` to $\mathbb{C}^{\times}$, and assume that the induced map $k \mapsto (\chi(k) : \mathbb{C})$, obtained by composing $\chi$ with the inclusion $\mathbb{C}^{\times} \hookrightarrow \mathbb{C}$, is continuous for the subspace topology on `rowIsometrySubgroup₀ ℝ` coming from $\mathrm{GL}_2(\mathbb{R})$. The assertion is then that there exists an integer $m$ with $\chi =$ `archWeightCharℝ` $m$, i.e. $\chi$ coincides with the character of that group attached to the weight $m$. Here the underlying notion of row isometry, for a normed field $K$, is that a matrix $k \in \mathrm{GL}_2(K)$ satisfies $\|\det k\| = 1$ together with $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x, y \in K$; such matrices form the subgroup `rowIsometrySubgroup K`, and `rowIsometrySubgroup₀ ℝ` is the group of real row isometries singled out in the project for the archimedean place.
--
--   This is the classification of the continuous one-dimensional characters of the rotation group $\mathrm{SO}(2,\mathbb{R})$: they are exactly the integral powers $r(\theta) \mapsto e^{im\theta}$, the continuity hypothesis being essential since the circle group has abundantly many discontinuous characters. It is used to convert an abstract one-dimensional type at a real place into an integer weight, and is cited in the decomposition of elements of the archimedean cut submodule into components with a prescribed archimedean character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous.lean

import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_eq_archWeightCharReal_of_continuous
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ)
    (hχ : Continuous fun k : rowIsometrySubgroup₀ ℝ => ((χ k : ℂˣ) : ℂ)) :
    ∃ m : ℤ, χ = archWeightCharℝ m := by sorry
