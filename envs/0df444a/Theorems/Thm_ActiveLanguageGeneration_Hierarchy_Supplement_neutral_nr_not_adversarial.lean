-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_nr_not_adversarial
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_nr_not_adversarial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:26:47.549842+00:00
-- url     : https://prove2.me/theorems/a9579acc-597d-4f63-a39c-2ba1e85a821e
-- title:
--   Theorem 3.8 — neutral NR generation without adversarial generation
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. There is a collection $C$ of infinite languages over $U$ that is neutrally generatable in the limit without repetition but is not adversarially generatable in the limit, even with repetition:
--
--   $$
--   C\in\mathrm{Neu}_{\mathrm{NR}}\setminus\mathrm{Adv}_{\mathrm R}.
--   $$
--
--   This gives $\mathrm{Adv}_{\mathrm R}\subsetneq\mathrm{Neu}_{\mathrm{NR}}$ in Theorem 1.1. The result is unconditional; the non-closure of adversarial generation under unions, cited from prior work in the paper, is not assumed.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.8, printed p.14 (PDF p.15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.8, printed p.14 (PDF p.15), on an ω-ordered universe. No cited separation is
assumed. -/
theorem neutral_nr_not_adversarial (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] :
    ∃ C : LanguageCollection U,
      NeutralLimitGeneratable .NR C ∧ ¬ AdversarialLimitGeneratable .R C := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
