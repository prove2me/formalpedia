-- Prove2me | Theorems.Thm_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero
-- name    : CuspForm.traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/1236cea6-eb29-571c-921a-ddf9826877b5
-- title:
--   U_q stabilises the q-new kernel of the trace pair
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, let $A$ be an Atkin–Lehner datum for $(M,q)$ — that is, a natural number $A.R$ together with the relation $M = q\,A.R$ and integers $a,b$ with $q a - A.R\, b = 1$ — let $q$ be prime, and assume $q \mid M$. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(M)$. Write $w$ for the Atkin–Lehner map [`CuspForm.atkinLehnerLin A 2`](def/CuspForm_AtkinLehnerOperator.html#L41), the $\mathbb{C}$-linear endomorphism of weight-$2$ cusp forms on $\Gamma_0(M)$ whose underlying function is $g \mapsto g \mid_2 A.\mathrm{alGL}$, and write $\operatorname{Tr}$ for [`CuspForm.traceLin A hq`](def/CuspForm_LevelLoweringTrace.html#L18), the $\mathbb{C}$-linear map from weight-$2$ cusp forms on $\Gamma_0(M)$ to weight-$2$ cusp forms on $\Gamma_0(A.R)$ whose underlying function is $g \mapsto g + U_q(g \mid_2 A.\mathrm{alGL})$, where $U_q h = \sum_{j<q} h \mid_2 \,\mathrm{heckeMatrix}\,q\,j$. Assume $\operatorname{Tr} f = 0$ and $\operatorname{Tr}(w f) = 0$. Then both $\operatorname{Tr}(U_q f) = 0$ and $\operatorname{Tr}(w (U_q f)) = 0$, where $U_q$ on forms is [`CuspForm.heckeULin 2 hqM`](def/ModularForm_HeckeOperatorForms.html#L83), the endomorphism of weight-$2$ cusp forms on $\Gamma_0(M)$ induced by the above summation operator.
--
--   This is the stability of the $q$-new subspace $\ker \operatorname{Tr} \cap \ker(\operatorname{Tr} \circ w_q)$ under the Hecke operator $U_q$ at a prime $q$ dividing the level, the case in which $U_q$ does not commute with the trace to level $M/q$. It is used in the construction of normalised eigenforms that are new at $q$ from Hecke-algebra support data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero.lean

import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero {M q : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) (hqM : q ∣ M) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (h1 : CuspForm.traceLin A hq f = 0) (h2 : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) = 0) :
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hqM f) = 0 ∧
      CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 (CuspForm.heckeULin 2 hqM f)) = 0 := by sorry
