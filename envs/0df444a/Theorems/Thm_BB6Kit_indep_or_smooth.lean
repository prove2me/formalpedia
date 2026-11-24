-- Prove2me | Theorems.Thm_BB6Kit_indep_or_smooth
-- name    : BB6Kit.indep_or_smooth
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:13:05.091739+00:00
-- url     : https://prove2.me/theorems/574f8a0d-19bd-41b7-a4b9-4d03151209b5
-- title:
--   $2,c,3$ are multiplicatively independent unless $c=2^a3^b$
-- statement:
--   **Lemma.** For every positive integer $c$, either $2,c,3$ are multiplicatively independent (`BB6Kit.MultIndep 2 c 3`), or $c=2^a3^b$ for some $a,b\ge 0$. Elementary (unique factorisation). It splits `BB6Kit.kit_bound` into the non-degenerate case (three logarithms) and the degenerate case (two logarithms).
-- source:
--   Elementary (unique factorisation); BB(6) Baker roadmap.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem indep_or_smooth (c : ℕ) (hc : 0 < c) :
    BB6Kit.MultIndep 2 c 3 ∨ ∃ a b : ℕ, c = 2 ^ a * 3 ^ b := by
  sorry
end BB6Kit
