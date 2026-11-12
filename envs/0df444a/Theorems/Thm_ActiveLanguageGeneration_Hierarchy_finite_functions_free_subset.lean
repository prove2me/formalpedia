-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_finite_functions_free_subset
-- name    : ActiveLanguageGeneration.Hierarchy.finite_functions_free_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T21:16:42.511006+00:00
-- url     : https://prove2.me/theorems/1af7a213-a31e-44b4-b9f8-8614a3bbfeae
-- title:
--   Lemma 3.3 — simultaneous infinite free subset
-- statement:
--   Let $X\subseteq\mathbb N_{>0}$ be infinite, let $I$ be a finite index set (possibly empty), and for every $i\in I$ let $r_i\ge1$ and $g_i:X_{\ne}^{r_i}\to\mathbb N_{>0}$. There exists an infinite subset $Y\subseteq X$ such that for every $i\in I$ and every ordered tuple $(y_1,\ldots,y_{r_i})$ of distinct elements of $Y$,
--
--   $$
--   g_i(y_1,\ldots,y_{r_i})\notin Y\setminus\{y_1,\ldots,y_{r_i}\}.
--   $$
--
--   The same set $Y$ works simultaneously for all functions and every ordering of the tuple entries. This is the free-subset statement used by the active hierarchy lower bound. The functions need not be computable or surjective; “range N” in the source specifies their codomain.
--
--   Differences from the source:
--   - encoding: the positive integers N → the positive-natural type ℕ+; reason: this is exactly the paper’s convention N = {1,2,…}, rather than a carrier containing zero
--   - encoding: a finite collection of functions, each with positive arity r(g) → an arbitrary finite index type ι, an arity map ι → ℕ+, and a dependent family of functions; reason: finite indexing allows varying arities and the empty collection; repeated identical indexed functions impose the same conditions
--   - encoding: all ordered distinct tuples from Y ⊆ X → embeddings Fin (r i) ↪ X whose underlying range is contained in Y; reason: restriction to Y and inclusion back into X identify exactly these tuple domains without changing any function value
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Lemma 3.3, printed p.7 (PDF p.8), proof printed pp.7–8 (PDF pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_DistinctTuple

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Lemma 3.3, printed p.7 (PDF p.8): a simultaneous free subset for any finite,
possibly empty, family with arbitrary positive arities and positive-integer codomain.
The word "range" in the paper specifies the codomain, not surjectivity. -/
theorem finite_functions_free_subset
    (X : Set ℕ+) (hX : X.Infinite) {ι : Type} [Fintype ι]
    (r : ι → ℕ+) (g : (i : ι) → DistinctTuple X (r i : ℕ) → ℕ+) :
    ∃ Y : Set ℕ+, Y ⊆ X ∧ Y.Infinite ∧
      ∀ (i : ι) (a : DistinctTuple X (r i : ℕ)), tupleValues a ⊆ Y →
        g i a ∉ Y \ tupleValues a := by sorry

end ActiveLanguageGeneration.Hierarchy
