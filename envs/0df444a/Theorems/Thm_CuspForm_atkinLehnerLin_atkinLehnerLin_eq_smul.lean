-- Prove2me | Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul
-- name    : CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/6b9ad0ba-295e-5936-9eb7-c6be173d4b14
-- title:
--   w_q² = q^{k-2} on cusp forms for Γ₀(M)
-- statement:
--   Fix natural numbers $M$ and $q$ with $M$ nonzero, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$: that is, a natural number $R$ with $M = q R$ together with integers $a, b$ satisfying the Bézout relation $q a - R b = 1$. Let $k$ be an integer and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(M)$. The operator [`CuspForm.atkinLehnerLin W k`](def/CuspForm_AtkinLehnerOperator.html#L41) is the $\mathbb{C}$-linear endomorphism of the space of weight-$k$ cusp forms for $\Gamma_0(M)$ whose value on $f$ has underlying function the weight-$k$ slash $f \mid[k] W.\mathrm{alGL}$ of $f$ by the element of $\mathrm{GL}_2(\mathbb{R})^{+}$ attached to the datum (the resulting function again being $\Gamma_0(M)$-invariant of weight $k$, holomorphic, and vanishing at the cusps). The assertion is that applying this operator twice to $f$ returns the scalar multiple $(q : \mathbb{C})^{k-2} \cdot f$, the exponent being the integer $k - 2$; the identity holds in the space of weight-$k$ cusp forms for $\Gamma_0(M)$, not merely for the underlying functions.
--
--   This is the classical composition law for the Atkin–Lehner operator $w_q$ on $S_k(\Gamma_0(M))$, reflecting the fact that the square of the matrix attached to the datum is $q$ times an element of $\Gamma_0(M)$. In weight $2$ it specialises to the statement that $w_q$ is an involution, which in turn forces every $w_q$-eigenvalue to be a square root of unity — the shape of the relation $a_q^2 = 1$ at bad primes for newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul.lean

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.atkinLehnerLin W k (CuspForm.atkinLehnerLin W k f) = ((q : ℂ) ^ (k - 2)) • f := by sorry
