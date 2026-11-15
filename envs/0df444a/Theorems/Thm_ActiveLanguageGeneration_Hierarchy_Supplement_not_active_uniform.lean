-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_not_active_uniform
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.not_active_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:29:11.253129+00:00
-- url     : https://prove2.me/theorems/349b2d49-9852-4d90-8554-73d8d6943308
-- title:
--   Theorem B.2 — some collection is not actively uniformly generatable
-- statement:
--   Let $U$ be a countably infinite universe. There is a collection $C$ of infinite languages over $U$ that is not actively uniformly generatable: for no positive integer $k$ is $C$ actively $k$-generatable (with repetition).
--
--   $$
--   \exists C\ \forall k\ge1:\quad C\notin\mathrm{Act}^{k}_{\mathrm R}.
--   $$
--
--   Uniform generation asks for one threshold valid for all targets; this shows it is genuinely stronger than active generation in the limit with repetition, which every collection satisfies.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
--   - encoding: k ∈ N = {1,2,...}; 'for any finite k' → k : ℕ with 0 < k (inside the generatability predicates, and as ∀ k, 0 < k → …); reason: the paper's N is the positive integers; the predicates are false at k = 0, so nothing outside the source's domain is asserted
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem B.2, printed p.27 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem B.2, printed p.27 (PDF p.28): some collection is not actively `k`-generatable
(with repetition) for any positive `k`. -/
theorem not_active_uniform (U : Type) [Countable U] [Infinite U] :
    ∃ C : LanguageCollection U, ∀ k : ℕ, 0 < k → ¬ ActiveKGeneratable .R C k := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
