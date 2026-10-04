-- Prove2me | Theorems.Thm_CookPvsNP_stack_lookup
-- name    : CookPvsNP.stack_lookup
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:59:52.054202+00:00
-- url     : https://prove2.me/theorems/8658b15d-8d23-4e7a-8c31-60383917031a
-- title:
--   stack lookup
-- statement:
--   Indexed lookup preserves the input and index, restores scratch, and returns the getD symbol with cost bounded by nine times both lengths plus thirteen.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackLookup
open CookPvsNP

namespace CookPvsNP
theorem stack_lookup {K A : Type} [DecidableEq K] (r : Fin 6 ↪ K) (fallback : A)
    (s : K → List A) (h2 : s (r 2) = []) (h3 : s (r 3) = [])
    (h4 : s (r 4) = []) (h5 : s (r 5) = []) :
    ∃ n ≤ 9 * (s (r 0)).length + 9 * (s (r 1)).length + 13,
      (lookupProg r fallback).Exec s
        (Function.update s (r 2) [(s (r 0)).getD (s (r 1)).length fallback]) n := by sorry
end CookPvsNP
