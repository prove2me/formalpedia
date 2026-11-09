-- Prove2me | Theorems.Thm_ForestPersuasion_Symmetric_lp_2_tightness
-- name    : ForestPersuasion.Symmetric.lp_2_tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:36.360199+00:00
-- url     : https://prove2.me/theorems/784d86b3-e5af-4ad8-ab39-0c1908951cff
-- title:
--   §5 — every feasible LP (2) value is inducible; the LP optima coincide
-- statement:
--   Fix a valid forest persuasion model and a monotone function $f:\{0,\ldots,n\}\to\mathbb R_{\ge0}$. Put $u(S)=f(|S|)$. Every LP (1) feasible point is feasible in LP (2). Conversely, every LP (2) feasible point $X$ has an actual signaling scheme $\Sigma$ with
--   $$V(\Sigma)=\operatorname{obj}(X).$$
--   Moreover, both LPs attain a common greatest objective value:
--   $$\max_{X\in\mathrm{LP}(1)}\operatorname{obj}(X)=\max_{X\in\mathrm{LP}(2)}\operatorname{obj}(X).$$
--   The realization claim and the equality of attained optima are both asserted. This establishes tightness of the relaxation under the symmetric-utility hypothesis.
--
--   Differences from the source:
--   - encoding: receivers 1,...,n and a directed forest → Fin n and an acyclic optional-parent map; reason: a relabelling of the same finite rooted forests; receiver i observes every coordinate in its reflexive descendant set
--   - generalization: n receivers with n implicitly positive → n may also be zero; reason: the empty forest has one joint signal vector and constant sender value u(∅); every positive-size instance is retained
--   - reading: distributions over an abstract signal set → PMFs over arbitrary M : Type, with no finite-support or cardinality bound; reason: the Bayes formula uses point masses and Appendix B footnote 6 explicitly works with discrete distributions; Lemma 5 attains the same optimum with finite support
--   - encoding: Bayes posteriors and expected sender utility → zero posterior on zero-mass observations, ENNReal nonnegative expectations converted to real; reason: full-support prior makes such observations null in both states, and finite-domain sender utilities make all expectations finite
--   - encoding: indices l=0,...,m with increasing distinct values τ_l → the subtype of distinct grid values, one coordinate per receiver; reason: the increasing enumeration tau is supplied and gives a bijective reindexing of the same grid
--   - encoding: LP equalities and nonnegative variables → two opposite inequality rows per equality plus identity rows in the published PrimalFeasible interface; reason: the feasible points and the maximization objective are unchanged
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §5, proof of Theorem 9, LP (2) tightness claim, PDF pp. 13–14 (printed pp. 12–13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_LPs

open scoped NNReal ENNReal

namespace ForestPersuasion.Symmetric

/-- Both tightness clauses in §5 (PDF pp. 13–14), and the relaxation direction.
The realized value and the common optima are exact, with no restriction on f. -/
theorem lp_2_tightness {n : ℕ} (I : Model n) (hI : I.Valid)
    (f : Fin (n + 1) → ℝ≥0) (hf : Monotone f) :
    (∀ X : Weights I, LP1Feasible I X → LP2Feasible I X) ∧
    (∀ X : Weights I, LP2Feasible I X →
      ∃ (M : Type) (σ : Scheme n M), value I (symmetricUtility f) σ =
        objective I (symmetricUtility f) X) ∧
    (∃ v : ℝ,
      IsGreatest (lpValues I (symmetricUtility f) (LP1Feasible I)) v ∧
      IsGreatest (lpValues I (symmetricUtility f) (LP2Feasible I)) v) := by sorry

end ForestPersuasion.Symmetric
