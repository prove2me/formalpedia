-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_lemma7_18_borel_selector
-- name    : BertsekasShreve.SemicontSelection.lemma7_18_borel_selector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:23.862361+00:00
-- url     : https://prove2.me/theorems/0651ab90-2dc8-4b51-a04a-99e08c32fbbe
-- title:
--   Lemma 7.18 — a Borel-measurable selector on the nonempty closed subsets of a compact metric space
-- statement:
--   Let $Y$ be a compact metric space with metric $d$, and let $2^Y$ be the collection of closed subsets of $Y$, topologized by the Hausdorff metric, which on nonempty sets is
--
--   $$\rho(A,B)=\max\Bigl\{\max_{a\in A}d(a,B),\ \max_{b\in B}d(b,A)\Bigr\}.$$
--
--   Then there is a Borel-measurable function $\sigma:2^Y-\{\emptyset\}\to Y$ such that
--
--   $$\sigma(A)\in A\qquad\text{for every nonempty closed }A\subseteq Y .$$
--
--   That is, one can choose a point of each nonempty closed set in a way that depends Borel-measurably on the set. Composed with the Borel-measurable set-valued map of Lemma 7.20, this selector produces the minimizing selector of Proposition 7.33.
--
--   **Formalization Note** In a compact space the nonempty closed sets are exactly the nonempty compact sets, so $2^Y-\{\emptyset\}$ is Mathlib's `NonemptyCompacts Y` with its Hausdorff extended metric (on nonempty sets this is the book's $\rho$, Appendix C, Definition C.1). It carries the Borel σ-algebra of that topology, and $Y$ its Borel σ-algebra. The book says "compact metrizable"; the statement is made for every compatible metric, and by Proposition C.1 the topology of $2^Y$ does not depend on the choice.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 151, Lemma 7.18; Appendix C, p. 303, Definition C.1

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.18 (Bertsekas & Shreve, p. 151). Let `Y` be a compact metric space. There is a
Borel-measurable `σ : 2^Y − {∅} → Y` with `σ(A) ∈ A` for every nonempty closed `A ⊆ Y`.
Here `2^Y − {∅}` is `NonemptyCompacts Y` (in a compact space the nonempty closed sets are the
nonempty compact sets) with the topology of the Hausdorff metric, and it carries its Borel
σ-algebra. -/
theorem lemma7_18_borel_selector {Y : Type*} [MetricSpace Y] [CompactSpace Y] :
    ∃ σ : NonemptyCompacts Y → Y,
      @Measurable _ _ (borel (NonemptyCompacts Y)) (borel Y) σ ∧ ∀ A : NonemptyCompacts Y, σ A ∈ A := by sorry

end BertsekasShreve.SemicontSelection
