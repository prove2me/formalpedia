-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_countable_active_identifiable
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.countable_active_identifiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:31:35.767194+00:00
-- url     : https://prove2.me/theorems/9c5aaf65-f597-4fbe-988b-d88c4c2ca755
-- title:
--   Theorem C.2 — every countable collection is actively 1-identifiable
-- statement:
--   Let $U$ be a countably infinite universe and let $C=\{L_1,L_2,\ldots\}$ be a countable collection of infinite languages over $U$ with an explicit indexing. Then $C$ is actively $1$-identifiable: there is an identifier $G:U^\star\to\mathbb N$ such that every language $K$ of the collection has a full repetition-free enumeration $x_1,x_2,\ldots$ with
--
--   $$
--   L_{G(x_1,\ldots,x_t)}=K\qquad\text{for all } t\ge1 .
--   $$
--
--   Active presentation thus makes identification of countable collections immediate.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
--   - encoding: a countable collection C = {L1, L2, …} → an arbitrary indexing Ls : ℕ → Language U (repetitions allowed), from 0; reason: every nonempty countable collection has such an indexing and finite ones are covered by repetition; the empty collection is vacuously identifiable
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem C.2, printed p.34 (PDF p.35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_ActiveIdentification

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem C.2, printed p.34 (PDF p.35): every explicitly indexed countable collection is
actively 1-identifiable. Repetitions in the indexing are allowed, which covers finite
collections. -/
theorem countable_active_identifiable (U : Type) [Countable U] [Infinite U]
    (Ls : ℕ → Language U) : ActiveKIdentifiable Ls 1 := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
