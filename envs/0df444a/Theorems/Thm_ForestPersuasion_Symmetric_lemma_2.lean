-- Prove2me | Theorems.Thm_ForestPersuasion_Symmetric_lemma_2
-- name    : ForestPersuasion.Symmetric.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:12.621706+00:00
-- url     : https://prove2.me/theorems/26a485bb-0d6d-4f64-9c94-e63ddfd28d92
-- title:
--   Lemma 2 — discretisation to the threshold grid
-- statement:
--   Fix a valid forest persuasion model with any monotone nonnegative sender set utility $u$. For every signaling scheme $\Sigma$ over any signal type, there exists a scheme $\Sigma'$ over a possibly different signal type such that
--   $$\Pr_{\Sigma'}[p_i\in\Theta\text{ for every }i]=1,\qquad V(\Sigma')\ge V(\Sigma).$$
--   The almost-sure condition is imposed on both state-conditional distributions. No symmetry assumption is made on $u$. This is the discretisation result used throughout the paper.
--
--   Differences from the source:
--   - encoding: receivers 1,...,n and a directed forest → Fin n and an acyclic optional-parent map; reason: a relabelling of the same finite rooted forests; receiver i observes every coordinate in its reflexive descendant set
--   - generalization: n receivers with n implicitly positive → n may also be zero; reason: the empty forest has one joint signal vector and constant sender value u(∅); every positive-size instance is retained
--   - reading: distributions over an abstract signal set → PMFs over arbitrary M : Type, with no finite-support or cardinality bound; reason: the Bayes formula uses point masses and Appendix B footnote 6 explicitly works with discrete distributions; Lemma 5 attains the same optimum with finite support
--   - encoding: Bayes posteriors and expected sender utility → zero posterior on zero-mass observations, ENNReal nonnegative expectations converted to real; reason: full-support prior makes such observations null in both states, and finite-domain sender utilities make all expectations finite
--   - encoding: indices l=0,...,m with increasing distinct values τ_l → the subtype of distinct grid values, one coordinate per receiver; reason: the increasing enumeration tau is supplied and gives a bijective reindexing of the same grid
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), Lemma 2; Appendix B, PDF p. 8 (printed p. 7), proof PDF pp. 20–22 (printed pp. 19–21). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_Grid

open scoped NNReal ENNReal

namespace ForestPersuasion.Symmetric

/-- Lemma 2 (PDF p. 8; proof pp. 20–22), with all §2 assumptions.
The new scheme may use a different unrestricted signal type. -/
theorem lemma_2 {n : ℕ} (I : Model n) (hI : I.Valid)
    (u : SenderUtility n) (hu : MonotoneUtility u) {M : Type} (σ : Scheme n M) :
    ∃ (M' : Type) (σ' : Scheme n M'),
      GridSupported I σ' ∧ value I u σ ≤ value I u σ' := by sorry

end ForestPersuasion.Symmetric
