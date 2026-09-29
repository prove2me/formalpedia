-- Prove2me | Theorems.Thm_CuspFormClass_isZeroAt_heckeT
-- name    : CuspFormClass.isZeroAt_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/5abc8999-77a2-5cb0-bba7-bacfd5d3df35
-- title:
--   Vanishing of Tₚ f at the cusps of Γ
-- statement:
--   Let $F$ be a type of functions from the upper half-plane $\mathbb{H}$ to $\mathbb{C}$ (via a `FunLike` instance), let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ which is arithmetic in the sense of `Subgroup.IsArithmetic`, let $k \in \mathbb{Z}$, and assume $F$ is a class of cusp forms of weight $k$ on $\Gamma$ (`CuspFormClass F Γ k`: holomorphy, weight-$k$ invariance under $\Gamma$, and vanishing at all cusps of $\Gamma$). Let $f : F$, let $p$ be a natural number, and let $c \in \mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` satisfy `IsCusp c Γ`. Then the function $$\mathrm{heckeT}\,k\,p\,f \;=\; \sum_{j < p} f \mid_k \mathrm{heckeMatrix}\,p\,j \;+\; f \mid_k \mathrm{heckeDiagMatrix}\,p$$ is zero at $c$ in the sense of `OnePoint.IsZeroAt … k`, i.e. for every $g \in \mathrm{GL}_2(\mathbb{R})$ carrying $\infty$ to $c$ the weight-$k$ slash of this function by $g$ tends to $0$ along the filter at $i\infty$. Here $\mathrm{heckeDiagMatrix}\,p$ is the identity for $p = 0$ and $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ otherwise, and $\mathrm{heckeMatrix}\,p\,j$ is the identity for $p = 0$ and $\begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ otherwise. No condition relating $p$ to the level of $\Gamma$ is assumed.
--
--   This is the cusp condition for the weight-$k$ Hecke operator $T_p$: applying $T_p$ to a cusp form again gives a function vanishing at every cusp of $\Gamma$. It supplies the `zero_at_cusps` component needed to package $T_p f$ as a cusp form, and is used in the construction of Hecke-eigenform bases and in the comparison of eigenforms of different level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspFormClass.isZeroAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k := by sorry
