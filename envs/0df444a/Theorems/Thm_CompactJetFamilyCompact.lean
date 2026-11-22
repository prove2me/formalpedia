-- Prove2me | Theorems.Thm_CompactJetFamilyCompact
-- name    : CompactJetFamilyCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:21:43.902836+00:00
-- url     : https://prove2.me/theorems/55de0a88-94b5-4829-91ea-f5c026fdcf89
-- title:
--   Compact Jet Family Compact: Compact Jet Family Compact
-- statement:
--   The paper's compact family is compact.  This is the conclusion of the paper's
--   sentence "by eq:first and the Arzela-Ascoli theorem, the family is compact", and it
--   is stated in exactly the closure form that Arzela-Ascoli delivers, which is also the
--   form in which the paper writes the family.
--
--   The two obligations the compactness theorem imposes are both supplied by the
--   first-order estimate: pointwise containment of every jet in the fixed compact set
--   `Icc (-1) 1 ×ˢ closedBall 0 C₀`, and equicontinuity of the jets, which comes from the
--   gradient bound for the first component and the `kappa`-Holder bound for the second.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CompactJetFamilyCompact.lean#L13-L105
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CompactJetFamilyCompact.lean#L13-L105

import Definitions.Def_PHigherOrder_CompactJetFamily
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_CompactJetFamilyCompact
import Theorems.Thm_PHarmJetEquicontinuity

set_option autoImplicit false

theorem CompactJetFamilyCompact (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) :
    IsCompact (CompactJetFamily p) := by sorry
