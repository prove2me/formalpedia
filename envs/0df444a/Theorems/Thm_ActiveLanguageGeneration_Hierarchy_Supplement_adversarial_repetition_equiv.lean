-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_adversarial_repetition_equiv
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.adversarial_repetition_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:27:47.422231+00:00
-- url     : https://prove2.me/theorems/3174df9c-50b6-4447-b0fa-2a31eb559783
-- title:
--   Theorem 3.9 — adversarial generation: repetition does not matter
-- statement:
--   Let $U$ be a countably infinite universe. A collection $C$ of infinite languages over $U$ is adversarially generatable in the limit without repetition if and only if it is adversarially generatable in the limit with repetition:
--
--   $$
--   C\in\mathrm{Adv}_{\mathrm{NR}}\iff C\in\mathrm{Adv}_{\mathrm R}.
--   $$
--
--   This is the equality $\mathrm{Adv}_{\mathrm{NR}}=\mathrm{Adv}_{\mathrm R}$ of Theorem 1.1; both directions are asserted.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.9, printed p.15 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.9, printed p.15 (PDF p.16): both directions. -/
theorem adversarial_repetition_equiv (U : Type) [Countable U] [Infinite U]
    (C : LanguageCollection U) :
    AdversarialLimitGeneratable .NR C ↔ AdversarialLimitGeneratable .R C := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
