-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_coe_eq_alSlash
-- name    : CuspForm.exists_gamma1_coe_eq_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/6ef5b80a-6421-5b81-bf86-f8b47ba4ef04
-- title:
--   Atkin–Lehner slash preserves cusp forms on Γ₁(M)
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$: that is, a natural number $R$ with $M = qR$ together with integers $a, b$ satisfying the Bézout relation $qa - Rb = 1$ (so in particular $q$ and $R$ are coprime and $q \mid M$). Let $k$ be an integer and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(M)$, in Mathlib's sense of `CuspForm`. The datum $W$ determines an integral $2 \times 2$ matrix `AtkinLehnerDatum.mat` of determinant $q$, and `AtkinLehnerDatum.alGL` is its image in $\mathrm{GL}_2(\mathbb{R})$, which is invertible because $q > 0$. The assertion is that there exists a cusp form $g$ of weight $k$ for $\Gamma_1(M)$ whose underlying function $\mathbb{H} \to \mathbb{C}$ coincides with [`ModularForm.alSlash W k`](def/ModularForm_AtkinLehnerDatum.html#L141) applied to the underlying function of $f$, i.e. with the weight-$k$ slash $f \mid[k] W.\mathrm{alGL}$. Thus the Atkin–Lehner slash of a weight-$k$ cusp form on $\Gamma_1(M)$ is again such a cusp form; the conclusion is phrased as existence of a cusp form with the prescribed underlying function, not as a linear operator on the space of cusp forms.
--
--   This is the statement that the Atkin–Lehner operator $W_q$ at a unitary divisor $q \mid M$ acts on the space $S_k(\Gamma_1(M))$, the starting point for the Atkin–Lehner theory of oldforms and newforms. It is used in the treatment of the Atkin–Lehner operators together with the diamond operators, in particular by [`CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH`](thm.html#CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH) and by the integrality statement for $q$-expansions of such slashes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_coe_eq_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_alSlash
    (M q : ℕ) [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f := by sorry
