-- Prove2me | Theorems.Thm_CuspForm_exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul
-- name    : CuspForm.exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/b39a5e6c-190f-5a65-b7bb-d38a497b02e4
-- title:
--   Two-cusp q-expansion principle mod p in weight two
-- statement:
--   Fix $M \ge 1$ and a prime $p$ with $p \mid M$ and $p^2 \nmid M$, and let $H$ be a subgroup of $(\mathbb Z/M)^\times$ containing every unit whose image under the reduction map $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ is $1$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb Z)$, the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb Z/M)^\times$ sending $\gamma$ to its lower-right entry modulo $M$. Let $L$ denote [`CuspForm.twoCuspLattice M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L86), the span over the smallest subring of $\mathbb C$ (so the $\mathbb Z$-span) of those weight-two cusp forms $f$ on $\Gamma_H(M)$ for which, for every $t$ in the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ at $(M,p)$ — that is, $R \in \mathbb N$ with $M = pR$ together with $a,b \in \mathbb Z$ satisfying $pa - Rb = 1$ — and every $n$, the $n$-th coefficient of the $q$-expansion at $\infty$ (period $1$) of $t f$ and of $(t f)\mid_2 W$ is a rational integer. Let $y \in L$ be such that every $q$-expansion coefficient of $y$, and every $q$-expansion coefficient of $y \mid_2 W$ for every Atkin–Lehner datum $W$ at $(M,p)$, is $p$ times a rational integer. Then there is $z \in L$ with $y = p \cdot z$.
--
--   This is the two-cusp $q$-expansion principle modulo $p$ for the Hecke-stable integral lattice of weight-two cusp forms on $\Gamma_H(M)$ with $p \| M$: vanishing of the reduction at both cusps forces divisibility by $p$ inside the lattice itself. It is used in the analysis of forms whose reductions vanish on both components of the special fibre, feeding the statements [`CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap`](thm.html#CuspForm.intTwoCuspGenMod_genU_self_intTwoCuspReduce_eq_zero_of_forall_qCoeff_eq_mul_of_isInfReductionMap) and [`ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash`](thm.html#ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.exists_mem_twoCuspLattice_eq_smul_of_forall_qCoeff_eq_mul_of_forall_qCoeff_alSlash_eq_mul
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))
    (h0 : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑y) n = (p : ℂ) * m)
    (hW : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ), ∃ m : ℤ,
      ModularFormClass.qCoeff (ModularForm.alSlash W 2 (⇑y)) n = (p : ℂ) * m) :
    ∃ z ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ), y = (p : ℂ) • z := by sorry
