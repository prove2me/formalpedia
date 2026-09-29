-- Prove2me | Theorems.Thm_CuspFormClass_isZeroAt_slash_ratCast
-- name    : CuspFormClass.isZeroAt_slash_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e34a085e-052d-5fdf-b0df-ddf47827bc99
-- title:
--   Slashing a cusp form by a rational matrix preserves vanishing at cusps
-- statement:
--   Let $F$ be a type equipped with a coercion to functions from the upper half-plane $\mathbb{H}$ to $\mathbb{C}$, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ carrying the arithmeticity instance `Subgroup.IsArithmetic`, let $k$ be an integer, and assume $F$ is a class of weight-$k$ cusp forms for $\Gamma$ in the sense of `CuspFormClass F Γ k` (so every $f : F$ is holomorphic, invariant under the weight-$k$ slash action of $\Gamma$, and vanishes at all cusps of $\Gamma$). Let $f : F$, let $g \in \mathrm{GL}_2(\mathbb{Q})$, and let $c$ be a point of the one-point compactification $\mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` which is a cusp of $\Gamma$, i.e. `IsCusp c Γ`. Write $\iota(g) \in \mathrm{GL}_2(\mathbb{R})$ for the image of $g$ under the entrywise map induced by the ring homomorphism $\mathbb{Q} \to \mathbb{R}$. The conclusion is that the slashed function $f \mid_k \iota(g) : \mathbb{H} \to \mathbb{C}$ satisfies `OnePoint.IsZeroAt c (f ∣[k] ι(g)) k`, that is, it vanishes at the cusp $c$ in the weight-$k$ sense, even though $\iota(g)$ need not lie in $\Gamma$ and $f \mid_k \iota(g)$ need not be $\Gamma$-invariant.
--
--   This is the standard statement that the cusp condition for a cusp form is stable under the weight-$k$ action of rational matrices, the point being that vanishing of $f \mid_k \iota(g)$ at $c$ is vanishing of $f$ at the cusp $\iota(g)\,c$. It supplies the cusp conditions for the Hecke operators $U_p$ and $T_p$ on cusp forms, and through these is used in the treatment of the $\Gamma_0$-level operators and of diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspFormClass_isZeroAt_slash_ratCast.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspFormClass.isZeroAt_slash_ratCast {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c (SlashAction.map k (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g) ⇑f) k := by sorry
