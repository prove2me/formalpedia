-- Prove2me | Theorems.Thm_CookPvsNP_CanonicalBlockParser_success_exact_shape
-- name    : CookPvsNP.CanonicalBlockParser.success_exact_shape
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:13:49.572288+00:00
-- url     : https://prove2.me/theorems/fc740bab-f75d-4e81-ad5d-0e23321f1905
-- title:
--   Successful canonical block parses have an exact natural-number encoding
-- statement:
--   If the canonical block parser halts with a successful top status marker, then its input consists of the canonical encoding of a natural number followed by the returned unread tail. The returned digit stack is exactly the reversed canonical binary digits of that number, and the second status marker confirms that a separator was read. This holds for every execution, including executions started on malformed input.

import Definitions.Def_CookPvsNP_CanonicalBlockParser
open CookPvsNP ProjSchedTW.Complexity

namespace CookPvsNP.CanonicalBlockParser

theorem success_exact_shape (input status rest digits markerTail : List BSym) (steps : ℕ)
    (h : CookPvsNP.CanonicalBlockParser.parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input [] status)
      (CookPvsNP.CanonicalBlockParser.store rest digits (.one :: markerTail)) steps) :
    ∃ n : ℕ, input = encNat n ++ rest ∧
      digits = (n.bits.map (fun b ↦ if b then BSym.one else BSym.zero)).reverse ∧
      markerTail = .one :: status := by
  sorry

end CookPvsNP.CanonicalBlockParser
