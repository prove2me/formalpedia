-- Prove2me | Theorems.Thm_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix
-- name    : CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/4f93f9cc-6075-594d-af90-153a8b63af06
-- title:
--   Trace of the second oldform embedding is T_q
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for $(M,q)$: a natural number $R = W.R$ together with integers $a,b$ such that $M = q R$ and $q a - R b = 1$. Assume $q$ is prime; by `ModularForm.AtkinLehnerDatum.not_dvd_R` the Bézout relation forces $q \nmid R$. Let $f$ be a weight-$2$ cusp form for $\Gamma_0(R)$ and $g$ a weight-$2$ cusp form for $\Gamma_0(M)$, and assume that the underlying function of $g$ is $f \mid_2 \mathrm{diag}(q,1)$, where $\mathrm{diag}(q,1)$ is the invertible real $2\times 2$ matrix $!![q,0;0,1]$ (the second oldform embedding of $f$). The conclusion is an identity of weight-$2$ cusp forms for $\Gamma_0(R)$: the image of $g$ under the trace map `traceLin`, whose underlying function is $g + U_q\bigl(f \mid_2 W.\mathrm{alGL}\bigr)$ with $U_q h = \sum_{j<q} h \mid_2 \mathrm{heckeMatrix}\,q\,j$, coincides with the image of $f$ under the Hecke operator `heckeTLin`, whose underlying function is $U_q f + f \mid_2 \mathrm{diag}(q,1)$.
--
--   This computes the level-lowering trace from $\Gamma_0(M)$ to $\Gamma_0(R)$, $M = qR$, on the second of the two oldform embeddings of a weight-$2$ cusp form of level $R$, the answer being the Hecke operator $T_q$; together with the value of the trace on the first embedding it gives the entries of the trace pairing matrix $\begin{pmatrix} q+1 & T_q \\ T_q & q+1\end{pmatrix}$ used in congruence and level-raising arguments. It is used in the proof of [`CuspForm.traceLin_rescaleLin`](thm.html#CuspForm.traceLin_rescaleLin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.lean

import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup
open scoped ModularForm MatrixGroups
namespace ModularForm.AtkinLehnerDatum

variable {M q : ℕ} [NeZero M] (W : AtkinLehnerDatum M q)

lemma not_dvd_R (hq : 1 < q) : ¬ q ∣ W.R := by
  intro ⟨t, ht⟩
  have h : (q : ℤ) ∣ 1 := ⟨W.a - (t : ℤ) * W.b, by
    rw [← W.bezout, ht]; push_cast; ring⟩
  exact absurd (Int.eq_one_of_dvd_one (by exact_mod_cast q.zero_le) h)
    (by exact_mod_cast hq.ne')

end ModularForm.AtkinLehnerDatum

theorem CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix {M q : ℕ}
    (W : ModularForm.AtkinLehnerDatum M q) [NeZero M] (hq : q.Prime)
    {f : CuspForm (Gamma0 W.R) 2} {g : CuspForm (Gamma0 M) 2}
    (hg : ⇑g = (⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    traceLin W hq g = heckeTLin (2 : ℤ) hq (W.not_dvd_R hq.one_lt) f := by sorry
