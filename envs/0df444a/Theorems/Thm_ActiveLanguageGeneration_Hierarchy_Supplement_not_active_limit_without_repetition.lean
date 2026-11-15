-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_not_active_limit_without_repetition
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.not_active_limit_without_repetition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:24:16.185528+00:00
-- url     : https://prove2.me/theorems/00bd56e3-00d0-4fe5-bb9c-1bff5c086982
-- title:
--   Theorem 3.2 — some collection is not actively generatable without repetition
-- statement:
--   Let $U$ be a countably infinite universe. There is a collection $C$ of infinite languages over $U$ that is not actively generatable in the limit without repetition: for every generator $G$ some $L\in C$ admits no full repetition-free enumeration on which $G$ is eventually correct while never repeating any earlier output.
--
--   Together with Theorem 3.1 this gives $\mathrm{Act}_{\mathrm{NR}}\subsetneq\mathrm{Act}_{\mathrm R}$.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.2, printed p.7 (PDF p.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.2, printed p.7 (PDF p.8). -/
theorem not_active_limit_without_repetition (U : Type) [Countable U] [Infinite U] :
    ∃ C : LanguageCollection U, ¬ ActiveLimitGeneratable .NR C := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
