-- Prove2me | Theorems.Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH
-- name    : CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/fa275d0a-a30b-57a6-9ea8-ce6b8bd50a18
-- title:
--   Square of the Atkin–Lehner slash equals p^{k-2}⟨ d⟩
-- statement:
--   Fix $M\ge 1$ and a natural number $p$ dividing $M$, so that $M/p$ divides $M$ and reduction induces a homomorphism $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$. Let $H\le(\mathbb Z/M)^\times$ be a subgroup containing every unit whose image in $(\mathbb Z/(M/p))^\times$ is $1$, and let $W$ be an Atkin–Lehner datum for $(M,p)$, that is, a natural number $R$ with $M=pR$ together with integers $a,b$ satisfying $pa-Rb=1$; its associated integral matrix, of determinant $p$, is viewed as an element `W.alGL` of $\mathrm{GL}(2,\mathbb R)$, and [`ModularForm.alSlash W k`](def/ModularForm_AtkinLehnerDatum.html#L141) is the weight-$k$ slash action by that element. Let $k\in\mathbb Z$ and let $d\in(\mathbb Z/M)^\times$ have image $p$ in $\mathbb Z/(M/p)$. Finally let $f$ be a weight-$k$ cusp form for the group $\Gamma_H(M)\le \mathrm{SL}(2,\mathbb Z)$, the image in $\mathrm{SL}(2,\mathbb Z)$ of the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H$ modulo $M$. The assertion is the equality of functions on the upper half-plane
--   $$(f\mid_k W)\mid_k W = p^{\,k-2}\cdot \langle d\rangle f,$$
--   where $\langle d\rangle f$ is [`CuspForm.diamondLinH k d f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the slash of $f$ by a chosen lift of $d$ to $\Gamma_0(M)$.
--
--   This is the relation $W_p^2=p^{k-2}\langle p\rangle_{M/p}$ for the Atkin–Lehner operator at $p$ on cusp forms of level $\Gamma_H(M)$, with $H$ large enough to contain the units congruent to $1$ modulo $M/p$; for $H=(\mathbb Z/M)^\times$ it reduces to the $\Gamma_0(M)$ statement, where the diamond operator is trivial. It is used in the analysis of the Atkin–Lehner involution on forms of level $\Gamma_H(M)$, in particular by the results producing a cusp form as an Atkin–Lehner slash or as a combination of $U_p$-, Atkin–Lehner- and diamond-translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH
    (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : ZMod (M / p)) = (p : ZMod (M / p)))
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W k (ModularForm.alSlash W k (⇑f)) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) := by sorry
