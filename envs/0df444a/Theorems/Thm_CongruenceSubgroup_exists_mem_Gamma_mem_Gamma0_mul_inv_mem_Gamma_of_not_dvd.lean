-- Prove2me | Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
-- name    : CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/5096705e-0acf-5599-b5fe-da360d930adc
-- title:
--   Approximation of SL₂(ℤ) modulo q inside Γ(ℓ)∩Γ₀(M')
-- statement:
--   Let $q$ be a prime, let $M'$ be a non-zero natural number with $q \nmid M'$, let $\ell$ be a prime with $\ell \neq q$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$. The assertion is that there exists $\delta \in \mathrm{SL}_2(\mathbb{Z})$ satisfying four conditions simultaneously: $\delta$ lies in the principal congruence subgroup $\Gamma(\ell)$, i.e. $\delta \equiv I \pmod{\ell}$ entrywise; $\delta$ lies in $\Gamma_0(M')$, i.e. its lower-left entry is divisible by $M'$; and both $\gamma\delta^{-1}$ and $\delta^{-1}\gamma$ lie in $\Gamma(q)$, i.e. $\delta$ agrees with $\gamma$ modulo $q$ on both sides. Thus $\gamma$ can be approximated modulo $q$ by an element of $\Gamma(\ell) \cap \Gamma_0(M')$, the two-sided form of the congruence being recorded explicitly rather than deduced from normality of $\Gamma(q)$.
--
--   This is the elementary strong-approximation (Chinese remainder) statement that $\Gamma(\ell)\cap\Gamma_0(M')$ surjects onto $\mathrm{SL}_2(\mathbb{Z}/q)$, giving the factorisation $\Gamma_0(M') = (\Gamma(q)\cap\Gamma_0(M'))\cdot(\Gamma(\ell)\cap\Gamma_0(M'))$ in either order. It is used in the analysis of level structures on modular curves, in particular in the study of the level automorphisms acting on Drinfeld-type charts and their fibres at a prime dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma ℓ ∧ δ ∈ CongruenceSubgroup.Gamma0 M' ∧
      γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma q ∧ δ⁻¹ * γ ∈ CongruenceSubgroup.Gamma q := by sorry
