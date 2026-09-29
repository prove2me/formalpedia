-- Prove2me | Theorems.Thm_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul
-- name    : CuspForm.sq_eq_one_of_atkinLehnerLin_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/1ecd8b8f-01f8-5211-83ad-425f01022df4
-- title:
--   Atkin–Lehner eigenvalues on S₂(Γ₀(M)) square to 1
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$, that is, a factorisation $M = qR$ with $R$ a natural number together with integers $a,b$ satisfying the Bézout relation $qa - Rb = 1$. Let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(M)$, assumed non-zero, and let $\lambda$ be a complex number such that $f$ is an eigenvector with eigenvalue $\lambda$ for the linear endomorphism [`CuspForm.atkinLehnerLin W 2`](def/CuspForm_AtkinLehnerOperator.html#L41) of the space of weight-$2$ cusp forms on $\Gamma_0(M)$, the operator that sends a cusp form $g$ to the weight-$2$ slash $g \mid_{2} W.\mathrm{alGL}$ of $g$ by the matrix attached to the datum $W$ (this slash again satisfies the $\Gamma_0(M)$ invariance, is holomorphic and vanishes at the cusps, so lands in the same space). Then $\lambda^2 = 1$.
--
--   This is the classical statement that the Atkin–Lehner operator $w_q$ acts on $S_2(\Gamma_0(M))$ as an involution, so its eigenvalues are $\pm 1$. It is used in the treatment of the behaviour of newforms at primes exactly dividing the level, feeding [`CuspForm.qCoeff_sq_eq_one_of_isNewform`](thm.html#CuspForm.qCoeff_sq_eq_one_of_isNewform), [`CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero`](thm.html#CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero) and [`CuspForm.isNewAt_or_goodEigensystemOccursAt`](thm.html#CuspForm.isNewAt_or_goodEigensystemOccursAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul.lean

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.sq_eq_one_of_atkinLehnerLin_eq_smul {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ≠ 0)
    {lam : ℂ} (hlam : CuspForm.atkinLehnerLin W 2 f = lam • f) : lam ^ 2 = 1 := by sorry
