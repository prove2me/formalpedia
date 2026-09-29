-- Prove2me | Theorems.Thm_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
-- name    : CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/b700a347-b0a7-594d-9659-b65cecfa8e62
-- title:
--   Vanishing at cusps of (f|_kσ)|_kdiag(ℓ,1)
-- statement:
--   Fix a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, a weight $k \in \mathbb{Z}$, a nonzero natural number $\ell$, and an element $\sigma$ of $\Gamma_0(M)$. Let $\Gamma_H(M)$ denote the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, namely the image in $\mathrm{SL}(2,\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose associated unit $\gamma_{11} \bmod M$ of $(\mathbb{Z}/M)^{\times}$ lies in $H$, regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$. Let $F$ be a type of functions from the upper half plane to $\mathbb{C}$ carrying a `CuspFormClass` structure for $\Gamma_H(M)$ in weight $k$, and let $f \in F$. Let $c \in \mathbb{R} \cup \{\infty\}$ be a cusp of $\Gamma_H(M)$. The conclusion is that the function obtained from $f$ by the weight-$k$ slash action of the image of $\sigma$ in $\mathrm{GL}(2,\mathbb{R})$, followed by the weight-$k$ slash action of [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21), i.e. of $\mathrm{diag}(\ell,1)$, is zero at $c$ in weight $k$.
--
--   This is the cusp condition for the degeneracy term $(f|_k\sigma)|_k\mathrm{diag}(\ell,1)$, $\tau \mapsto \ell^{k-1}(f|_k\sigma)(\ell\tau)$, occurring among the representatives of the classical Hecke operator $T_\ell$ on cusp forms for $\Gamma_H(M)$. It feeds the verification that the Hecke-type operators preserve cuspidality, and is cited by [`CuspForm.stableT`](thm.html#CuspForm.stableT).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c
      ((⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) ∣[k]
        ModularForm.heckeDiagMatrix ℓ) k := by sorry
