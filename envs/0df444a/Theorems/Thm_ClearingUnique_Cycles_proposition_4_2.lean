-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_proposition_4_2
-- name    : ClearingUnique.Cycles.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:53.749983+00:00
-- url     : https://prove2.me/theorems/d2437ea4-1ef6-416e-a4b3-ad7d9fd0901b
-- title:
--   Proposition 4.2, p. 12 — a differing row has zero equity
-- statement:
--   Let $P^-$ and $P^+$ be respectively the least and greatest clearing payment matrices of a financial network $N$ satisfying the standing assumptions. If the row of agent $i$ in $P^-$ is strictly below its row in $P^+$, then both matrices give that agent zero equity:
--
--   $$
--   P^-_i<P^+_i\quad\Longrightarrow\quad e_i(P^-)=e_i(P^+)=0.
--   $$
--
--   This identifies the agents at which payment multiplicity can occur.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 12 (PDF 14), Proposition 4.2

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem proposition_4_2 (N : FinNetwork I) (hN : N.Standing)
    (Pm Pp : I → I → ℝ)
    (hm : IsLeast {P : I → I → ℝ | IsClearing N P} Pm)
    (hp : IsGreatest {P : I → I → ℝ | IsClearing N P} Pp)
    (i : I) (hrow : RowLt Pm Pp i) :
    equity N Pm i = 0 ∧ equity N Pp i = 0 := by sorry

end ClearingUnique.Cycles
