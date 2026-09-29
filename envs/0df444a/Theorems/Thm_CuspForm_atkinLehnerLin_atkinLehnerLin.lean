-- Prove2me | Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin
-- name    : CuspForm.atkinLehnerLin_atkinLehnerLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/7531d5f6-5847-56da-b513-c71e772a03bd
-- title:
--   The Atkin–Lehner operator is an involution in weight 2
-- statement:
--   Let $M$ be a nonzero natural number and $q$ a natural number, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$, that is: a natural number $R$ together with a proof that $M = qR$, and integers $a, b$ with $qa - Rb = 1$. For a weight $k$, the operator [`CuspForm.atkinLehnerLin W k`](def/CuspForm_AtkinLehnerOperator.html#L41) is the $\mathbb{C}$-linear endomorphism of the space $S_k(\Gamma_0(M))$ of cusp forms of weight $k$ for $\Gamma_0(M)$ that sends $f$ to the weight-$k$ slash $f \mid_k W.\mathrm{alGL}$ by the matrix attached to the datum, the resulting function being again invariant under $\Gamma_0(M)$, holomorphic and vanishing at the cusps. The assertion is that for every $f \in S_2(\Gamma_0(M))$, i.e. every cusp form of weight $2$ for $\Gamma_0(M)$, one has $$\mathrm{atkinLehnerLin}(W,2)\bigl(\mathrm{atkinLehnerLin}(W,2)(f)\bigr) = f,$$ so that in weight $2$ this operator is an involution of $S_2(\Gamma_0(M))$.
--
--   This is the classical Atkin–Lehner involution $W_q$ on $S_2(\Gamma_0(M))$ (the Fricke involution when $q = M$), the involutivity underlying the relation $a_q = -\lambda_q$ with $\lambda_q = \pm 1$ for $q$-newforms. It is used in the study of the weight-$2$ Hecke action, for instance in the computation of the determinant of $U_q$ on a newform's span and in the local analysis of the $p$-adic Galois representation of a newform at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_atkinLehnerLin_atkinLehnerLin.lean

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.atkinLehnerLin_atkinLehnerLin {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 f) = f := by sorry
