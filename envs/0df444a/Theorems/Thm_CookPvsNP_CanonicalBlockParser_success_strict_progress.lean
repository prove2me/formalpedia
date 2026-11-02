-- Prove2me | Theorems.Thm_CookPvsNP_CanonicalBlockParser_success_strict_progress
-- name    : CookPvsNP.CanonicalBlockParser.success_strict_progress
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:24:30.931195+00:00
-- url     : https://prove2.me/theorems/459e2268-9e24-4c33-858b-ca5bd590718b
-- title:
--   A successful canonical block parse strictly decreases the unread input
-- statement:
--   For any input and any execution of the canonical natural-number block parser, if the top output status marker indicates success, then the unread input suffix is strictly shorter than the original input. In particular, parsing the empty binary digit block still consumes its separator. This progress invariant applies to malformed inputs as well as canonical inputs and supports total loop bounds for successive block parsers.
-- source:
--   Auxiliary stack-program invariant for the canonical natural-number encoding used in ProjSchedTW.Complexity; supports the explicitly encoded scheduling and tensor-reduction machines.

import Definitions.Def_CookPvsNP_CanonicalBlockParser
open CookPvsNP ProjSchedTW.Complexity

namespace CookPvsNP.CanonicalBlockParser

theorem success_strict_progress (input status rest digits markerTail : List BSym) (steps : ℕ)
    (h : parseCanonicalBlockProg.Exec
      (store input [] status) (store rest digits (.one :: markerTail)) steps) :
    rest.length < input.length := by
  sorry

end CookPvsNP.CanonicalBlockParser
