-- Prove2me | Theorems.Thm_CookPvsNP_CanonicalBlockParser_execution_and_bounds
-- name    : CookPvsNP.CanonicalBlockParser.execution_and_bounds
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:36:10.527727+00:00
-- url     : https://prove2.me/theorems/192c1e29-fcc4-448b-81a7-a015ad6b507f
-- title:
--   Canonical binary block parser: correctness and total linear bound
-- statement:
--   The canonical binary block parser has two properties.
--
--   1. For a natural number $n$, a suffix $u$, and an initial status stack $s$, the parser started on $\operatorname{enc}(n)u$ consumes exactly the first block, leaves $u$ unread, stores the reversed digits of $n$, and pushes two success markers. This takes exactly $3\,|\operatorname{bits}(n)|+7$ source-program steps.
--   2. On every input word, including malformed and truncated blocks, the parser halts in at most $3|w|+7$ steps. Both the remaining input and the stored digit stack have length at most $|w|$.
--
--   This bounded parser can be composed with finite-stack implementations of binary reductions. The all-input property here is a termination and size bound; it does not by itself characterize acceptance of every malformed input.
-- source:
--   Supporting stack-machine implementation for binary encodings in Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. Parser behaviour and complexity are auxiliary formalization results, not claims from the paper.

import Mathlib
import Definitions.Def_CookPvsNP_CanonicalBlockParser

namespace CookPvsNP.CanonicalBlockParser

open CookPvsNP ProjSchedTW.Complexity

theorem execution_and_bounds :
    (∀ (n : ℕ) (tail status : List BSym),
      parseCanonicalBlockProg.Exec
        (store (encNat n ++ tail) [] status)
        (store tail (n.bits.map digitSym).reverse (.one :: .one :: status))
        (3 * n.bits.length + 7)) ∧
    (∀ input status : List BSym, ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
        steps ≤ 3 * input.length + 7 ∧ digits.length ≤ input.length ∧ rest.length ≤ input.length) := by sorry

end CookPvsNP.CanonicalBlockParser
