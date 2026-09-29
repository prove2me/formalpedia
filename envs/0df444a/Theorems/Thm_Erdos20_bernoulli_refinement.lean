-- Prove2me | Theorems.Thm_Erdos20_bernoulli_refinement
-- name    : Erdos20.bernoulli_refinement
-- status  : Proved
-- author  : @lunjia
-- created : 2026-09-26T17:17:07.188231+00:00
-- url     : https://prove2.me/theorems/d200580e-a23b-468b-ab9e-b92b72e68590
-- title:
--   Bernoulli refinement for an indexed spread family
-- statement:
--   Let $X$ be a finite ground set and $I$ a nonempty finite set of labels. Let $(B_i)_{i\in I}$ be an indexed family of subsets of $X$, allowing repeated and empty members. Suppose $R>0$, $0<\delta<1$, $R\delta>1$, and the family is normalized $R$-spread:
--
--   $$R^{|T|}\,|\{i\in I:T\subseteq B_i\}|\le |I|\qquad(T\subseteq X).$$
--
--   There is a deterministic choice of a label $\varphi(i,W)\in I$ for each label $i$ and subset $W\subseteq X$, satisfying
--
--   $$B_{\varphi(i,W)}\subseteq B_i\cup W,$$
--
--   such that for an independent Bernoulli $\delta$-sample $W$ of $X$,
--
--   $$\mathbb E_W\left[\frac{1}{|I|}\sum_{i\in I}|B_{\varphi(i,W)}\setminus W|\right]\le\frac{2\log 2}{\log(R\delta)}\,\frac{1}{|I|}\sum_{i\in I}|B_i|.$$
--
--   All logarithms are natural. The residual at each label is a subset of that label's original member. Keeping the labels preserves multiplicities when distinct residuals coincide, which makes this lemma suitable for repeated refinement.
--
--   **Source formulation.** This is the Bernoulli, indexed-family adaptation of the two-chain entropy refinement argument in Hu and Tao. In particular, it differs from the fixed-cardinality sampling formulation in Hu's Lemma 2; the Bernoulli proof gives the coefficient displayed above.
-- source:
--   L. Hu, Entropy Estimation via Two Chains (19 May 2021), Definition 1 and Lemma 2, https://theorydish.blog/2021/05/19/entropy-estimation-via-two-chains-streamlining-the-proof-of-the-sunflower-lemma/ ; T. Tao, The sunflower lemma via Shannon entropy (20 July 2020), Definition 1 and refinement argument, https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ . This is an indexed, normalized-spread Bernoulli adaptation of those arguments, not a verbatim restatement of the fixed-cardinality sampling lemma.

import Definitions.Def_SunflowerIndexedSpread
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
open scoped BigOperators Classical
open ProbabilityTheory

namespace Erdos20

theorem bernoulli_refinement
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Nonempty ι]
    (B : ι → Finset α) (R : ℝ) (δ : unitInterval)
    (hR : 0 < R) (hδ : 0 < (δ : ℝ)) (hδ1 : (δ : ℝ) < 1)
    (hRδ : 1 < R * (δ : ℝ)) (hB : IndexedSpread R B) :
    ∃ φ : ι → Set α → ι,
      (∀ i W, B (φ i W) ⊆ B i ∪ W.toFinset) ∧
      (∑ W : Set α, (setBernoulli Set.univ δ).real {W} *
        ((∑ i, ((B (φ i W) \ W.toFinset).card : ℝ)) / Fintype.card ι)) ≤
        (2 * Real.log 2 / Real.log (R * (δ : ℝ))) *
          ((∑ i, ((B i).card : ℝ)) / Fintype.card ι) := by sorry

end Erdos20
