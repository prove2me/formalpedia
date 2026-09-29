-- Prove2me | Theorems.Thm_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
-- name    : CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/11c97ae4-15da-52e0-b072-ac3be363d578
-- title:
--   Diamond operators preserve ℤ₍ₚ₎-integrality of q-expansions
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $k$ be an integer, $d \in (\mathbb{Z}/M)^\times$, and let $f$ be a cusp form of weight $k$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, namely the image in $\mathrm{SL}(2,\mathbb{Z})$ of the set of matrices in $\Gamma_0(M)$ whose lower-right entry reduces into $H$. Assume that every coefficient $\mathrm{qCoeff}(f)(n)$, $n \in \mathbb{N}$, of the $q$-expansion of $f$ of width $1$ lies in the image under $\mathbb{Q} \to \mathbb{C}$ of the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$, i.e. of $\mathbb{Z}_{(p)}$. The conclusion is that the same holds for all $q$-expansion coefficients of [`CuspForm.diamondLinH k d f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132): here [`CuspForm.diamondLinH k d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) is the $\mathbb{C}$-linear endomorphism of weight-$k$ cusp forms for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) given by the weight-$k$ slash action of a lift `gammaLift M d` of $d$ to $\mathrm{SL}(2,\mathbb{Z})$ when the cusp-vanishing condition [`CuspForm.StableD M H k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72) holds (that for all $\sigma \in \Gamma_0(M)$, all such $f$ and all cusps $c$ of the group, $f \mid_k \sigma$ vanishes at $c$), and is zero otherwise.
--
--   This is the statement that the diamond operator $\langle d \rangle$ preserves $\mathbb{Z}_{(p)}$-integrality of the Fourier expansion at $\infty$, for levels $M$ exactly divisible by $p$ and groups $\Gamma_H(M)$ whose $H$ contains the kernel of reduction modulo $M/p$. It feeds the results asserting that the set of cusp forms integral at two cusps is stable under the diamond operators, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (k : ℤ) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ))) :
    ∀ n : ℕ, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k d f)) n ∈
      ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) := by sorry
