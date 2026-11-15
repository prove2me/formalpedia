-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_finite_neutral_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.finite_neutral_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:28:14.843248+00:00
-- url     : https://prove2.me/theorems/1df8d86a-5920-4f64-bdf2-0de7b9872282
-- title:
--   Theorem 5.1 — strict finite neutral-generation hierarchy
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. For every integer $k\ge2$ there is a collection $C$ of infinite languages over $U$ that is neutrally $k$-generatable without repetition but is not neutrally $(k-1)$-generatable with repetition.
--
--   $$
--   \forall k\ge2\ \exists C:\quad C\in\mathrm{Neu}^{k}_{\mathrm{NR}}\setminus\mathrm{Neu}^{k-1}_{\mathrm R}.
--   $$
--
--   This is clause 1 of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 5.1, printed p.21 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 5.1, printed p.21 (PDF p.22), on an ω-ordered universe. -/
theorem finite_neutral_hierarchy (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] :
    ∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      NeutralKGeneratable .NR C k ∧ ¬ NeutralKGeneratable .R C (k - 1) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
