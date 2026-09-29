-- Prove2me | Theorems.Thm_CuspForm_exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice
-- name    : CuspForm.exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/f761db7d-2f83-5d4c-a933-1c24ff1786ce
-- title:
--   Atkin–Lehner congruence aₙ((Uₚy)∣ W)≡ -aₙ(⟨ d⟩ y)(mod p)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, and let $W$ be an Atkin–Lehner datum for $(M,p)$, that is, a natural number $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$. Let $d \in (\mathbb{Z}/M)^\times$ have image $p$ in $\mathbb{Z}/(M/p)$, and let $y$ belong to the two-cusp lattice [`CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)`](def/CuspForm_TwoCuspLattice.html#L86), the span over the prime subring $\mathbb{Z} \subseteq \mathbb{C}$ of those weight-two cusp forms $f$ on $\Gamma_H(M)$ (the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of matrices in $\Gamma_0(M)$ whose lower-right entry reduces into $H$) for which, for every $t$ in the Hecke ring [`CuspForm.heckeRingH M H 2`](def/CuspForm_TwoCuspLattice.html#L37), every Atkin–Lehner datum for $(M,p)$ and every index, all $q$-expansion coefficients at $\infty$ of $t f$ and of the $W$-slash of $t f$ are rational integers. Then for every $n \in \mathbb{N}$ there is an integer $m$ with $$a_n\bigl((U_p y)\mid_2 W\bigr) + a_n\bigl(\langle d\rangle y\bigr) = p\,m,$$ where $a_n$ denotes the $n$-th coefficient of the $q$-expansion of period $1$, $U_p$ is [`CuspForm.heckeULinH 2 p`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) (the operator $f \mapsto \mathrm{heckeU}\ 2\ p\ f$ when this preserves weight-two cusp forms on $\Gamma_H(M)$, and $0$ otherwise), $\langle d\rangle$ is [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) (slash by a lift of $d$ to $\Gamma_0(M)$ when this preserves weight-two cusp forms on $\Gamma_H(M)$, and $0$ otherwise), and $\mid_2 W$ is the weight-two slash by the Atkin–Lehner matrix of $W$ viewed in $\mathrm{GL}_2(\mathbb{R})$.
--
--   This is the integral form of the Atkin–Lehner relation $(U_p y)\mid_2 W_p \equiv -\langle p\rangle y \pmod p$ at the cusp $\infty$, valid on the two-cusp integral lattice in weight two for $\Gamma_H(M)$ with $p \| M$. It is used in the mod $p$ comparison of the $U_p$-stable and Atkin–Lehner-twisted integral structures, being cited by [`CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap`](thm.html#CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.exists_qCoeff_alSlash_heckeULinH_add_qCoeff_diamondLinH_eq_mul_of_mem_twoCuspLattice
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : ZMod (M / p)) = (p : ZMod (M / p)))
    (y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))) (n : ℕ) :
    ∃ m : ℤ, ModularFormClass.qCoeff
        (ModularForm.alSlash W 2 (⇑(CuspForm.heckeULinH 2 p (y : CuspForm (CohCarrier.GammaH M H) 2)))) n +
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d (y : CuspForm (CohCarrier.GammaH M H) 2))) n = (p : ℂ) * m := by sorry
