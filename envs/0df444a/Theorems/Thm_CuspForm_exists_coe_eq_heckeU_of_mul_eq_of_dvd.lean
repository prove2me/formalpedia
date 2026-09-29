-- Prove2me | Theorems.Thm_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd
-- name    : CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/78d75ee6-b00e-5894-a53d-c07a6d45f8b5
-- title:
--   U_q lowers the level when q² divides it
-- statement:
--   Let $m$, $q$, $R$ be natural numbers with $m$ nonzero, satisfying $qR = m$ and $q \mid R$ (so that $q^2 \mid m$ and $R = m/q$), and let $F$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(m)$. The assertion is that there is a cusp form $g$ of weight $2$ for $\Gamma_0(R)$ whose underlying function on the upper half-plane is equal to [`ModularForm.heckeU 2 q`](def/ModularForm_HeckeOperator.html#L93) applied to the function underlying $F$, that is, to the finite sum $\sum_{j=0}^{q-1} F \mid_2 A_{q,j}$, where $A_{q,j}$ is the matrix `heckeMatrix q j`, namely the image in $\mathrm{GL}_2(\mathbb{R})$ of $\begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}$ (and the identity when $q = 0$), and $\mid_2$ is the weight-$2$ slash action normalised by the determinant; explicitly the function is $\tau \mapsto q^{-1}\sum_{j=0}^{q-1} F\bigl((\tau+j)/q\bigr)$. The equality is an equality of functions on the upper half-plane, so the witness $g$ is determined uniquely.
--
--   This is the level-lowering property of the operator $U_q$ (Lemma 7 of Atkin–Lehner): when $q^2$ divides the level $m$, $U_q$ carries weight-$2$ cusp forms on $\Gamma_0(m)$ into weight-$2$ cusp forms on $\Gamma_0(m/q)$, here with $q$ not assumed prime. It is used in the proof of [`CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero`](thm.html#CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero), in the analysis of forms whose Fourier coefficients at indices prime to the level vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd
    {m q R : ℕ} [NeZero m] (hqR : q * R = m) (hq : q ∣ R)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 R) 2, ⇑g = ModularForm.heckeU 2 q ⇑F := by sorry
