-- Prove2me | Theorems.Thm_AutoformalisationSCI_theorem_A_4_degree_remarks
-- name    : AutoformalisationSCI.theorem_A_4_degree_remarks
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:35:19.342081+00:00
-- url     : https://prove2.me/theorems/b8de281c-dd12-4245-9619-5313a8dbe508
-- title:
--   Remarks after Theorem A.4 — complement and Turing degree of $d_l$
-- statement:
--   **Remarks following Theorem A.4** (p. 22). For every $l\ge 2$ and $k\ge 9$:
--   1. the complement of $d_l$ is $\Pi^0_l$-complete; and
--   2. $d_l$ has the Turing degree of $\emptyset^{(l)}$ (since $\emptyset^{(l)}$ is $\Sigma^0_l$-complete by Post's theorem).
--
--   These record the exact position of $d_l$ in both the many-one and the Turing degrees, complementing the $\Sigma^0_l$-completeness of Theorem A.4.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Paragraph following the proof of Theorem A.4, p. 22.

import Mathlib
import Definitions.Def_AutoformalisationSCI_Arith
import Definitions.Def_AutoformalisationSCI_Oracle
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem theorem_A_4_degree_remarks (l k : ℕ) (hl : 2 ≤ l) (hk : 9 ≤ k)
    (E : ComputablePolyEnum (l - 1 + k)) :
    PiComplete l (dSetL l k hl E)ᶜ ∧
      SetTuringEquivalent (dSetL l k hl E) (jumpIter l) := by sorry

end AutoformalisationSCI
