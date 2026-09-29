-- Prove2me | Theorems.Thm_FinitePowersetBernoulliFamilyMoment
-- name    : FinitePowersetBernoulliFamilyMoment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T20:44:33.424322+00:00
-- url     : https://prove2.me/theorems/8ef038b0-4743-4df9-a530-2aeb2d7a69ed
-- title:
--   Finite powerset Bernoulli-family moment identity
-- statement:
--   Let $S$ be a finite set, let $I$ be a finite index set, and let each index $i$ have a support set contained in $S$. For a real parameter $p$, the weighted sum over all subsets $X\subseteq S$ of the number of supports contained in $X$ equals the sum of the individual support weights:
--
--   $$
--   \sum_{X\subseteq S}p^{|X|}(1-p)^{|S\setminus X|}
--   \,\bigl|\{i\in I:\operatorname{support}(i)\subseteq X\}\bigr|
--   =
--   \sum_{i\in I}p^{|\operatorname{support}(i)|}.
--   $$
--
--   This moment identity is the probabilistic averaging step in the crossing-lemma argument, applied respectively to vertices, edges, and crossing points.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePowersetBernoulliFamilyMoment.lean#L1-L91

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset

open Classical
noncomputable section

lemma FinitePowersetBernoulliFamilyMoment {α ι : Type*}
    (S : Finset α) (I : Finset ι) (support : ι → Finset α)
    (hsupport : ∀ i ∈ I, support i ⊆ S) (p : ℝ) :
    ∑ X ∈ S.powerset,
        p ^ X.card * (1 - p) ^ (S \ X).card *
          ((I.filter fun i => support i ⊆ X).card : ℝ) =
      ∑ i ∈ I, p ^ (support i).card := by sorry
