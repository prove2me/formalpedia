-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_active_limit_all_with_repetition
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.active_limit_all_with_repetition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:23:38.507404+00:00
-- url     : https://prove2.me/theorems/815e5f6d-fc99-427c-a19c-c2be4c0aee0b
-- title:
--   Theorem 3.1 — every collection is actively generatable with repetition
-- statement:
--   Let $U$ be a countably infinite universe. Every collection $C$ of infinite languages over $U$, countable or not, is actively generatable in the limit with repetition: there is one generator $G$ such that every $L\in C$ has a full repetition-free enumeration $x_1,x_2,\ldots$ and a finite time $t^\star$ with
--
--   $$
--   G(x_1,\ldots,x_t)\in L\setminus\{x_1,\ldots,x_t\}\qquad\text{for all } t\ge t^\star .
--   $$
--
--   This is the equality $\mathrm{Act}_{\mathrm R}=\mathrm{All}$ of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.1, printed p.6 (PDF p.7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.1, printed p.6 (PDF p.7): every, possibly uncountable, collection of infinite
languages over a countably infinite universe is actively generatable in the limit with
repetition. -/
theorem active_limit_all_with_repetition (U : Type) [Countable U] [Infinite U]
    (C : LanguageCollection U) : ActiveLimitGeneratable .R C := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
