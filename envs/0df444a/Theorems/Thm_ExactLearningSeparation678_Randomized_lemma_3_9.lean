-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_lemma_3_9
-- name    : ExactLearningSeparation678.Randomized.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:20.322234+00:00
-- url     : https://prove2.me/theorems/e06c46d0-22e0-438a-b97f-ea3a8d32ac35
-- title:
--   Lemma 3.9 — adaptive equality-query replacement
-- statement:
--   Let $X,Z$ be finite sets with $Z$ nonempty and $|Z|=\ell$. Let $k\ge1$, and let $F:X\to Z$ have a law uniform and independent on every set of at most $k$ distinct inputs. Let $G:X\to Z$ be a uniformly random function. Fix any deterministic adaptive algorithm making at most $D$ equality queries, returning the bit $\mathbf1[F(x)=z]$ in the first experiment and $\mathbf1[G(x)=z]$ in the second. Its full transcript laws obey
--   $$d_{\rm TV}(T_F,T_G)\le\binom Dk(2/\ell)^k.$$
--   The learner may repeat queries and stop early. The statement covers arbitrary finite $X,Z$ and all budgets $D$, including $D<k$, when the bound is zero.
--
--   This is the general equality-query replacement lemma, independent of the paper's choice of field or polynomial family.
--
--   **Formalization Note** A finite carrier for the final output represents the finite range of a bounded decision tree. $k$-wise independence is read in its standard at-most-$k$ sense, including when $k>|X|$.
--
--   Differences from the source:
--   - reading: the explanatory phrase tests exactly k distinct inputs → uniform independent evaluations on every set of at most k distinct inputs; reason: the standard definition and the proof use inheritance to smaller sets; exact-k-only fails for X a singleton, Z={0,1}, k=2, deterministic F=0 and D=1, where TV=1/2 but the stated bound is zero
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
--   - encoding: an arbitrary deterministic algorithm with a bounded finite-alphabet transcript and a final output → a published Boolean decision tree with finite output carrier and a budget imposed on every oracle; reason: only finitely many outputs are reachable at bounded depth; unreachable histories can be truncated without affecting any experiment
--   - encoding: uniform label values and the expression 2/ℓ → Z is explicitly nonempty; reason: a uniform label law and the displayed reciprocal require a positive label cardinality
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 3.9 and proof, pp.24–25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Observations

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Lemma 3.9, pp.24–25. Reading: k-wise means uniform on every set of at most k inputs. Exact-k-only is vacuous for k>|X| and contradicts the displayed bound; the proof uses inheritance to smaller sets. Outputs have finite range, as every bounded tree on a finite alphabet does. -/
theorem lemma_3_9 {X Z O : Type} [Fintype X] [Fintype Z] [Nonempty Z]
    [DecidableEq Z] [Fintype O] (k D : ℕ) (hk : 1 ≤ k) (law : PMF (X → Z))
    (hF : KWiseUniform k law) (A : QAlgorithms.DecisionTree (X × Z) Bool O)
    (hA : A.MakesAtMost D) :
    tv (equalityLaw D A law) (equalityLaw D A (PMF.uniformOfFintype (X → Z))) ≤
      (D.choose k : ℝ) * (2 / (Fintype.card Z : ℝ)) ^ k := by sorry

end ExactLearningSeparation678.Randomized
