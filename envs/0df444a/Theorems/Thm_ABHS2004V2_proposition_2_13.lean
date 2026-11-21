-- Prove2me | Theorems.Thm_ABHS2004V2_proposition_2_13
-- name    : ABHS2004V2.proposition_2_13
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:20:58.447414+00:00
-- url     : https://prove2.me/theorems/0407d39d-32d5-4b15-8e15-6a6f80f7eff8
-- title:
--   Proposition 2.13 — Canonical forms of normal almost closed terms
-- statement:
--   The outer constructors of a normal affinely typed term with only token variables free are those prescribed by its type.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Proposition 2.13. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_TermSystem

namespace ABHS2004V2

/-- Proposition 2.13. A normal term with only diamond variables free has a
canonical outer form determined by its type. -/
theorem proposition_2_13 {w : Term} {τ : Ty}
    (ht : HasType w τ) (hac : IsAlmostClosed w) (hnorm : IsNormal w) :
    HasCanonicalNormalForm τ w := by sorry

end ABHS2004V2
