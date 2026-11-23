-- Prove2me | Theorems.Thm_BB6Baker_liouville_delta
-- name    : BB6Baker.liouville_delta
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T18:07:57.741179+00:00
-- url     : https://prove2.me/theorems/d76c115c-997a-44e1-a16b-417e98a84325
-- title:
--   Liouville step for integer α: the interpolation determinant is an integer, so $|\Delta| \ge 1$ when $\Delta \ne 0$
-- statement:
--   For positive-integer $\alpha_1,\alpha_2,\alpha_3$, the Mignotte–Voutier interpolation determinant $\Delta$ (definition `BB6Delta`) computed over $\mathbb R$ equals the integer determinant `deltaZ`. Hence $\Delta \ne 0$ implies $|\Delta| \ge 1$.
--
--   This replaces the Liouville inequality (Lemma 3.8 / Proposition 3.9 of arXiv:2205.08899) in the case of rational-integer $\alpha$'s, where it collapses to a nonzero integer having absolute value at least $1$. It is the arithmetic lower bound in the planned decomposition of `BB6Baker.bw_instance` for $(\alpha_1,\alpha_2,\alpha_3) = (2,c,3)$.
-- source:
--   Mignotte & Voutier, arXiv:2205.08899, Lemma 3.8 and Proposition 3.9 (specialised to integer α).

import Mathlib
import Definitions.Def_BB6Delta

namespace BB6Baker
theorem liouville_delta (N b1' b3' b2'' b3'' α1 α2 α3 : ℕ) (kml rst : Fin N → ℕ × ℕ × ℕ)
    (h : BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst ≠ 0) :
    BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst =
        (BB6Delta.deltaZ N b1' b3' b2'' b3'' α1 α2 α3 kml rst : ℝ) ∧
      1 ≤ |BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst| := by
  sorry
end BB6Baker
