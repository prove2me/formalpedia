-- Prove2me | Theorems.Thm_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg
-- name    : CuspForm.det_heckeULin_two_eq_pow_finrank_or_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/060015f7-e706-5e63-ae04-54d6cbe52193
-- title:
--   Determinant of Uₚ on S₂(Γ₀(Rp)) is ± p^{dim S₂(Γ₀(R))}
-- statement:
--   Let $p$ be a prime and $R$ a nonzero natural number with $p \nmid R$; the product $R p$ is then nonzero as well. Consider the $\mathbb{C}$-linear endomorphism [`CuspForm.heckeULin`](def/ModularForm_HeckeOperatorForms.html#L83) of weight $2$ for the divisibility $p \mid R p$, acting on the space of cusp forms of weight $2$ for $\Gamma_0(Rp)$: it sends a cusp form $f$ to the function $\sum_{j=0}^{p-1} f \mid_{2} \,\mathrm{heckeMatrix}\,p\,j$, the sum over the $p$ matrices indexing the operator $U_p$ of the weight-$2$ slash action on $f$, the result again being a cusp form for $\Gamma_0(Rp)$. The assertion is that the determinant of this endomorphism is either $p^{g}$ or $-p^{g}$, where $g = \dim_{\mathbb{C}} S_2(\Gamma_0(R))$ is the $\mathbb{C}$-dimension of the space of weight-$2$ cusp forms for $\Gamma_0(R)$; the exponent is `Module.finrank` of that space and the base is the image of $p$ in $\mathbb{C}$.
--
--   This is the determinant computation for the Atkin–Lehner operator $U_p$ in weight $2$ at a prime exactly dividing the level: on the $p$-old part $U_p$ acts through $2\times 2$ blocks of determinant $p$, and on the complement it agrees up to sign with the Atkin–Lehner involution $W_p$. It is used to bound the dimension of the kernel of $U_p$ on the mod $p$ reduction of the weight-$2$ cusp forms of level $Rp$, a step in the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.det_heckeULin_two_eq_pow_finrank_or_eq_neg
    (p : ℕ) [Fact p.Prime] (R : ℕ) [NeZero R] (hpR : ¬ p ∣ R) :
    haveI : NeZero (R * p) := ⟨Nat.mul_ne_zero (NeZero.ne R) (Fact.out : p.Prime).ne_zero⟩
    LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = (p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) ∨
      LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = -(p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) := by sorry
