-- Prove2me | Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
-- name    : CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/3de2aaa7-ee54-56b3-811d-3e2df6619c1d
-- title:
--   Atkin–Lehner W_q preserves cusp forms on Γ_H(M)
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$: a natural number $R$ together with a proof that $M = qR$ and integers $a,b$ with $qa - Rb = 1$. Let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$ and assume that $H$ contains every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` along the divisibility $q \mid M$ witnessed by $R$ is trivial, i.e. $H$ contains the kernel of reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/q)^{\times}$. Let $k$ be an integer and let $f$ be a cusp form of weight $k$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose lower right entry, read modulo $M$ as a unit, lies in $H$. Then there exists a cusp form $X$ of the same weight $k$ for the same group whose underlying function on the upper half plane equals [`ModularForm.alSlash W k ⇑f`](def/ModularForm_AtkinLehnerDatum.html#L141), that is $f \mid_k W_{\mathrm{alGL}}$, the weight-$k$ slash of $f$ by the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral Atkin–Lehner matrix of the datum (of determinant $q$).
--
--   This is the assertion that the Atkin–Lehner matrix at the exact divisor $q \parallel M$ normalises $\Gamma_H(M)$, hence that $W_q$ acts on $S_k(\Gamma_H(M))$, under the condition that the level structure encoded by $H$ is cut out by a congruence modulo $q$ alone. It is the basic compatibility behind later statements about $q$-expansions at the two cusps, the Fricke involution and Hecke operators on these spaces; the proof cites the conjugation relation $W \gamma = \delta W$ with $\delta \in \Gamma_0(M)$ recorded in [`ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq`](thm.html#ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (hHq : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro W.R W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑f := by sorry
