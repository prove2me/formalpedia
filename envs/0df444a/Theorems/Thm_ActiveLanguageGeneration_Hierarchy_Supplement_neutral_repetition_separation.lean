-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_repetition_separation
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_repetition_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:25:17.310195+00:00
-- url     : https://prove2.me/theorems/41fa480b-c3f8-4efe-9311-db8756be2945
-- title:
--   Theorem 3.5 — neutral 1-generation with repetition without neutral NR generation
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. There is a collection $C$ of infinite languages over $U$ that is neutrally $1$-generatable with repetition but is not neutrally generatable in the limit without repetition.
--
--   $$
--   \exists C:\quad C\in\mathrm{Neu}^{1}_{\mathrm R}\quad\text{and}\quad C\notin\mathrm{Neu}_{\mathrm{NR}} .
--   $$
--
--   It separates $\mathrm{Neu}_{\mathrm{NR}}\subsetneq\mathrm{Neu}_{\mathrm R}$ in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the universe of finite binary strings p and p#, ordered by length and then by 0 < 1 < # → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: the paper's ordered universe has order type ω, and every ω-ordered universe is order-isomorphic to it, so the existence statement transports
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.5, printed p.11 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.5, printed p.11 (PDF p.12), on an ω-ordered universe. -/
theorem neutral_repetition_separation (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] :
    ∃ C : LanguageCollection U,
      NeutralKGeneratable .R C 1 ∧ ¬ NeutralLimitGeneratable .NR C := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
