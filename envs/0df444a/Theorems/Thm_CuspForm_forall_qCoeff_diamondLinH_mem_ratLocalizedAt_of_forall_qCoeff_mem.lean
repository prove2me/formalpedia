-- Prove2me | Theorems.Thm_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem
-- name    : CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/3cb80b82-f6a3-5560-90b6-d31ee5936f67
-- title:
--   Diamond operators preserve two-cusp ℤ₍ₚ₎-integrality in weight two
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Fix $d \in (\mathbb{Z}/M)^\times$ and a weight-two cusp form $f$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), that is, the image in $SL(2,\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ whose lower-right entry mod $M$ lies in $H$. Assume that for every Atkin–Lehner datum $W$ for $(M,p)$ — a factorisation $M = p\,R$ together with integers $a,b$ satisfying $pa - Rb = 1$ — and every $n$, both the $n$-th coefficient of the width-one $q$-expansion of $f$ and that of $f \mid_2 W_{\mathrm{al}}$, the weight-two slash of $f$ by the real matrix attached to $W$, lie in the image in $\mathbb{C}$ of the subring $\{q \in \mathbb{Q} : p \nmid \mathrm{den}(q)\} = \mathbb{Z}_{(p)}$. Then the same two conditions hold for [`CuspForm.diamondLinH 2 d f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the diamond operator $\langle d\rangle$ in weight two, defined as the weight-two slash by a chosen $SL(2,\mathbb{Z})$-lift of $d$ when the predicate `StableD M H 2` holds and as the zero map otherwise.
--
--   This is the statement that naive two-cusp $\mathbb{Z}_{(p)}$-integrality of weight-two cusp forms on $\Gamma_H(M)$, measured at the cusp $\infty$ and after every Atkin–Lehner slash at the prime $p$ exactly dividing $M$, is stable under the diamond operators. It feeds the construction of the two-cusp integral set of forms used on the $p$-local side of the argument, via [`CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem`](thm.html#CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(f)) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(f)) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ))) :
    ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d f)) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d f)) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) := by sorry
