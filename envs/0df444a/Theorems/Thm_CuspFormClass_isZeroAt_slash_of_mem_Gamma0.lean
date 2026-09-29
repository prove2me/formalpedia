-- Prove2me | Theorems.Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0
-- name    : CuspFormClass.isZeroAt_slash_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/7ea2115d-5ad5-585e-8abd-4e4ac496bccd
-- title:
--   Slashing a cusp form by σ ∈ Γ₀(M) keeps cusp vanishing
-- statement:
--   Fix an integer $M \ge 1$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a weight $k \in \mathbb{Z}$ and an element $\sigma$ of $\Gamma_0(M) \le \mathrm{SL}_2(\mathbb{Z})$. Let $\Gamma_H(M)$ be the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to the class of its lower right entry (with inverse the class of its upper left entry); it is viewed inside $\mathrm{GL}_2(\mathbb{R})$ via the canonical map. Let $F$ be a type of functions on the upper half plane with values in $\mathbb{C}$ which is a `CuspFormClass` for this subgroup of $\mathrm{GL}_2(\mathbb{R})$ in weight $k$, and let $f : F$. Let $c \in \mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` be a cusp of that subgroup. The conclusion is that the weight-$k$ slash $f \mid_k \sigma$, where $\sigma$ is regarded as an element of $\mathrm{GL}_2(\mathbb{R})$, is zero at $c$ in weight $k$ in the sense of `OnePoint.IsZeroAt`.
--
--   This is the cusp-vanishing half of the statement that the diamond operators $\langle d \rangle$, realised as $f \mapsto f\mid_k\sigma$ for $\sigma \in \Gamma_0(M)$, preserve cusp forms for $\Gamma_H(M)$. It is used in the construction [`CuspForm.stableD`](thm.html#CuspForm.stableD), where the diamond action on the space of cusp forms of level $\Gamma_H(M)$ is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspFormClass.isZeroAt_slash_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k := by sorry
