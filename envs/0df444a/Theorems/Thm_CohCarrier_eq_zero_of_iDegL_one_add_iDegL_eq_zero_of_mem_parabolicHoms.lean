-- Prove2me | Theorems.Thm_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
-- name    : CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/dfa36a92-6151-5693-a2f9-0006f2d98404
-- title:
--   Joint injectivity of the two degeneracy pull-backs in weight two
-- statement:
--   Let $F$ be a field of characteristic zero, let $M$ be a nonzero natural number and $p$ a prime with $p \nmid M$ (and $Mp \neq 0$). Write $\Gamma_H(N,\top)$ for the subgroup `GammaH N ⊤` of $SL(2,\mathbb{Z})$, i.e. $\Gamma_0(N)$ viewed through the trivial condition on the lower-right reduction, and $H^1(N,\top,F) =$ `H1 N ⊤ F` for the $F$-module of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(N,\top) \to F$. Assume given `LevelLE` data for the pair $(M, Mp)$ with $d = 1$ and with $d = p$, that is: $M \mid Mp$, $d \mid (Mp)/M$, and the (vacuous, for $\top$) compatibility of unit reductions. For each such $d$ the map `iDegL` is the $F$-linear pull-back $H^1(M,\top,F) \to H^1(Mp,\top,F)$ along the homomorphism `iotaDeg` sending $\gamma \in \Gamma_H(Mp,\top)$ to its conjugate `conjLowerMat d γ` in $\Gamma_H(M,\top)$. Let $y_1, y_2 \in H^1(M,\top,F)$ both lie in [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62), the submodule of homomorphisms vanishing on every $\gamma$ whose matrix trace satisfies $\mathrm{tr}(\gamma)^2 = 4$. If the pull-back of $y_1$ by the $d=1$ map plus the pull-back of $y_2$ by the $d=p$ map is zero in $H^1(Mp,\top,F)$, then $y_1 = 0$ and $y_2 = 0$.
--
--   This is the weight-two, characteristic-zero statement that the two degeneracy maps from level $M$ to level $Mp$ are jointly injective on parabolic cohomology, so that the $p$-old part of $H^1(\Gamma_0(Mp))$ is a direct sum of two copies of parabolic cohomology at level $M$; via Eichler–Shimura it corresponds to the linear independence of $h_1(\tau)$ and $h_2(p\tau)$ for cusp forms of level $M$. It is used in bounding the dimension of Hecke eigenspaces in the corner of the old subspace at level divisible by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier

theorem CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
    {F : Type} [Field F] [CharZero F]
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (y₁ y₂ : H1 M ⊤ F)
    (hy₁ : y₁ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F)
    (hy₂ : y₂ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F)
    (h : iDegL M (M * p) ⊤ ⊤ 1 F F h1 y₁ + iDegL M (M * p) ⊤ ⊤ p F F hp y₂ = 0) :
    y₁ = 0 ∧ y₂ = 0 := by sorry
