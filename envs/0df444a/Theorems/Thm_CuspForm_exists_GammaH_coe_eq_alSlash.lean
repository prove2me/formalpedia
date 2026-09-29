-- Prove2me | Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
-- name    : CuspForm.exists_GammaH_coe_eq_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/52d715b2-58e9-5465-bc8d-126b30e58b52
-- title:
--   Atkin–Lehner slash preserves cusp forms on Γ_H(M)
-- statement:
--   Let $M$ be a nonzero natural number, let $p$ be a prime, and let $W$ be an Atkin–Lehner datum at $(M,p)$: a natural number $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$. Let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$ which, by hypothesis `hHp`, contains every unit of $\mathbb{Z}/M$ whose reduction along $R \mid M$ is trivial, i.e. $H$ contains the kernel of $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/R)^{\times}$. Let $k$ be an integer and let $F$ be a cusp form of weight $k$ for the group $\Gamma_H(M)$, defined as the image in $SL_2(\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ consisting of those matrices whose lower-right entry, viewed as a unit of $\mathbb{Z}/M$ via `gamma0Units`, lies in $H$. The conclusion asserts the existence of a cusp form $X$ of weight $k$ for the same group $\Gamma_H(M)$ whose underlying function $\mathbb{H} \to \mathbb{C}$ is $F \mid[k]\, W_{\mathbb{R}}$, where $W_{\mathbb{R}} =$ `W.alGL` is the element of $GL_2(\mathbb{R})$ obtained from the integral Atkin–Lehner matrix of the datum, of determinant $p$.
--
--   This is the statement that the Atkin–Lehner operator at $p$ maps $S_k(\Gamma_H(M))$ to itself, for $H$ containing the kernel of reduction to $(\mathbb{Z}/R)^{\times}$, phrased as the existence of a cusp form with the prescribed underlying function rather than as the construction of an operator. It is used in the analysis of $q$-expansions and integrality of Atkin–Lehner and diamond translates of cusp forms at level $\Gamma_H(M)$, and in the comparison of level $M$ with level $M/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_GammaH_coe_eq_alSlash.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_GammaH_coe_eq_alSlash
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑F := by sorry
