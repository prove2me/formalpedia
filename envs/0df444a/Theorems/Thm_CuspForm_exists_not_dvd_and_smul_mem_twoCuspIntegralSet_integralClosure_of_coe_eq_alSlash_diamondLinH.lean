-- Prove2me | Theorems.Thm_CuspForm_exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
-- name    : CuspForm.exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/69d10038-656b-5950-889c-8aa2b706c48d
-- title:
--   Prime-to-p multiple of ⟨ e⟩ f∣ W_d is two-cusp integral
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Let $W_d$ be an Atkin–Lehner datum for the pair $(M, M/p)$, that is, a natural number $R$ with $M = (M/p)\cdot R$ together with integers $a,b$ satisfying $(M/p)a - Rb = 1$; let $e \in (\mathbb{Z}/M)^\times$, and let $f$ be a weight-two cusp form for the group $\Gamma_H(M)$, realised as the image in $SL(2,\mathbb{Z})$ of the preimage of $H$ under the determinant-type character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$. Assume $f$ lies in the two-cusp integral set at $p$ over the bottom subring $\bot \subseteq \mathbb{C}$ (the image of $\mathbb{Z}$): for every element $t$ of the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th coefficient of the width-one $q$-expansion of $t f$ and of $(t f)\mid_2 W$ is a rational integer. Let $X$ be a weight-two cusp form for $\Gamma_H(M)$ whose underlying function on the upper half-plane equals $(\langle e\rangle f)\mid_2 W_d$, where $\langle e\rangle =$ `diamondLinH 2 e` is slashing by a lift of $e$ to $SL(2,\mathbb{Z})$ when the cusp-vanishing condition `StableD` holds and is $0$ otherwise, and $\mid_2 W_d$ is the weight-two slash by the matrix attached to $W_d$. Then there exists a natural number $D$ with $p \nmid D$ such that $D\cdot X$ lies in the two-cusp integral set at $p$ over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$: all the above coefficients of $t(D\cdot X)$ and of $(t(D\cdot X))\mid_2 W$ are algebraic integers.
--
--   This is the form-theoretic half of the $p$-integrality of an Atkin–Lehner–diamond translate in the two-cusp setting, clearing denominators by a factor prime to $p$ so that integrality over $\overline{\mathbb{Z}}$ is preserved along the whole Hecke orbit and at both cusp classes. It feeds [`CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure`](thm.html#CuspForm.exists_not_dvd_and_coe_eq_smul_alSlash_diamond_and_mem_twoCuspIntegralSet_integralClosure), and through it the level-lowering comparison of $q$-expansions at the two cusps of $\Gamma_H(M)$ with $p \| M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) :
    ∃ D : ℕ, ¬ p ∣ D ∧
      ((D : ℂ) • X : CuspForm (CohCarrier.GammaH M H) 2) ∈
        CuspForm.twoCuspIntegralSet M H 2 p (integralClosure ℤ ℂ).toSubring := by sorry
