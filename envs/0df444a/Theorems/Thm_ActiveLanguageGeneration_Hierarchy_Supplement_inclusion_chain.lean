-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_inclusion_chain
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.inclusion_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:22:34.634057+00:00
-- url     : https://prove2.me/theorems/a46b5f6a-c719-424b-abf0-c4748718deaa
-- title:
--   Theorem 1.1 — inclusion chain of generation in the limit
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. Write $\mathrm{Adv}_q$, $\mathrm{Neu}_q$ and $\mathrm{Act}_q$ for the sets of collections of infinite languages over $U$ that are adversarially, neutrally (for $\prec$) and actively generatable in the limit, with repetition ($q=\mathrm R$) or without repetition ($q=\mathrm{NR}$), and let $\mathrm{All}$ be the set of all collections of infinite languages over $U$. Then
--
--   $$
--   \mathrm{Adv}_{\mathrm{NR}}=\mathrm{Adv}_{\mathrm R}\subsetneq\mathrm{Neu}_{\mathrm{NR}}\subsetneq\mathrm{Neu}_{\mathrm R}\subsetneq\mathrm{Act}_{\mathrm{NR}}\subsetneq\mathrm{Act}_{\mathrm R}=\mathrm{All}.
--   $$
--
--   The chain places the three presentation models and the two repetition conventions in one total order of strength.
--
--   **Formalization Note** All six links are stated: two equalities and four strict inclusions.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: A ⊊ B → A ⊂ B (A ⊆ B and not B ⊆ A); reason: Mathlib's strict subset of sets; identical meaning
--   - encoding: All, the set of all language collections → Set.univ in the type of sets of infinite subsets of U; reason: a language is an infinite subset, so these are exactly all language collections
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 1.1, printed p.2 (PDF p.3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 1.1, printed p.2 (PDF p.3): `Adv_NR = Adv_R ⊊ Neu_NR ⊊ Neu_R ⊊ Act_NR ⊊ Act_R = All`
on one ω-ordered universe (linear order, finitely many predecessors, infinite), as sets of
collections of infinite languages. Each `⊂` is a strict inclusion (`⊆` and not `⊇`). -/
theorem inclusion_chain (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U] [Infinite U] :
    {C : LanguageCollection U | AdversarialLimitGeneratable .NR C} =
        {C | AdversarialLimitGeneratable .R C} ∧
    {C : LanguageCollection U | AdversarialLimitGeneratable .R C} ⊂
        {C | NeutralLimitGeneratable .NR C} ∧
    {C : LanguageCollection U | NeutralLimitGeneratable .NR C} ⊂
        {C | NeutralLimitGeneratable .R C} ∧
    {C : LanguageCollection U | NeutralLimitGeneratable .R C} ⊂
        {C | ActiveLimitGeneratable .NR C} ∧
    {C : LanguageCollection U | ActiveLimitGeneratable .NR C} ⊂
        {C | ActiveLimitGeneratable .R C} ∧
    {C : LanguageCollection U | ActiveLimitGeneratable .R C} = Set.univ := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
