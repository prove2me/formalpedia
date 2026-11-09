-- Prove2me | Theorems.Thm_ForestPersuasion_Symmetric_lemma_5
-- name    : ForestPersuasion.Symmetric.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:22.778811+00:00
-- url     : https://prove2.me/theorems/8c239ea4-0752-48e1-a3af-459590e15590
-- title:
--   Lemma 5 — the sender optimum is the attained optimum of LP (1)
-- statement:
--   Fix a valid forest persuasion model with any monotone nonnegative sender set utility $u$. LP (1) is feasible, its objective is bounded above, and its objective-value image has greatest element
--   $$\max\{\operatorname{obj}(X):X\text{ feasible in LP (1)}\}=V^*.$$
--   The scheme-value set is also nonempty and bounded above, so the real supremum defining $V^*$ has no default-value case. The greatest-element conclusion includes attainment, rather than just equality of two possibly undefined suprema. This identifies the exact finite grid optimization problem for general monotone utilities.
--
--   Differences from the source:
--   - encoding: receivers 1,...,n and a directed forest → Fin n and an acyclic optional-parent map; reason: a relabelling of the same finite rooted forests; receiver i observes every coordinate in its reflexive descendant set
--   - generalization: n receivers with n implicitly positive → n may also be zero; reason: the empty forest has one joint signal vector and constant sender value u(∅); every positive-size instance is retained
--   - reading: distributions over an abstract signal set → PMFs over arbitrary M : Type, with no finite-support or cardinality bound; reason: the Bayes formula uses point masses and Appendix B footnote 6 explicitly works with discrete distributions; Lemma 5 attains the same optimum with finite support
--   - encoding: Bayes posteriors and expected sender utility → zero posterior on zero-mass observations, ENNReal nonnegative expectations converted to real; reason: full-support prior makes such observations null in both states, and finite-domain sender utilities make all expectations finite
--   - encoding: indices l=0,...,m with increasing distinct values τ_l → the subtype of distinct grid values, one coordinate per receiver; reason: the increasing enumeration tau is supplied and gives a bijective reindexing of the same grid
--   - encoding: the maximum V* over inducible information structures → the real supremum over values of actual schemes, with nonempty and bounded guards as conclusions; reason: a constant scheme is available and all utilities are bounded; Lemma 5 supplies attainment, so the supremum has the stated maximum value
--   - encoding: LP equalities and nonnegative variables → two opposite inequality rows per equality plus identity rows in the published PrimalFeasible interface; reason: the feasible points and the maximization objective are unchanged
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), Lemma 5; Appendix D, PDF p. 9 (printed p. 8), proof PDF pp. 23–24 (printed pp. 22–23). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_LPs

open scoped NNReal ENNReal

namespace ForestPersuasion.Symmetric

/-- Lemma 5 (PDF p. 9; proof pp. 23–24). The optimum is attained;
Vstar remains the supremum over actual signaling schemes. -/
theorem lemma_5 {n : ℕ} (I : Model n) (hI : I.Valid)
    (u : SenderUtility n) (hu : MonotoneUtility u) :
    (attainableValues I u).Nonempty ∧ BddAbove (attainableValues I u) ∧
    (∃ X : Weights I, LP1Feasible I X) ∧
    BddAbove (lpValues I u (LP1Feasible I)) ∧
    IsGreatest (lpValues I u (LP1Feasible I)) (Vstar I u) := by sorry

end ForestPersuasion.Symmetric
