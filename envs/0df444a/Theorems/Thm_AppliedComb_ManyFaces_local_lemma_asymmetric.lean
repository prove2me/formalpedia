-- Prove2me | Theorems.Thm_AppliedComb_ManyFaces_local_lemma_asymmetric
-- name    : AppliedComb.ManyFaces.local_lemma_asymmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:58:35.546792+00:00
-- url     : https://prove2.me/theorems/823daabd-fa2b-432e-a501-c77ba1d85ebb
-- title:
--   Lemma 16.14 — the Lovász Local Lemma, asymmetric form
-- statement:
--   Let $(\Omega, P)$ be a finite probability space and $\mathcal F = (A_i)_{i \in \iota}$ a finite family of events, indexed by a finite set $\iota$. For each $i$ let $N(i) \subseteq \iota \setminus \{i\}$ be a subfamily such that $A_i$ is independent of any event not in $N(i)$: for every subfamily $G \subseteq \iota$ with $i \notin G$ and $G \cap N(i) = \emptyset$,
--   $$P\Big(A_i \cap \prod_{j \in G}\overline{A_j}\Big) = P(A_i)\,P\Big(\prod_{j \in G}\overline{A_j}\Big),$$
--   where $\overline{A}$ is the complement of $A$ and $\prod_{j\in G}\overline{A_j} = \bigcap_{j\in G}\overline{A_j}$. Suppose that for each $i$ there is a real number $x(i)$ with $0 < x(i) < 1$ such that
--   $$P(A_i) \le x(i) \prod_{j \in N(i)} \big(1 - x(j)\big).$$
--   Then for every non-empty subfamily $G \subseteq \iota$,
--   $$P\Big(\prod_{i \in G}\overline{A_i}\Big) \;\ge\; \prod_{i \in G}\big(1 - x(i)\big).$$
--   In particular, the probability that all events of $\mathcal F$ fail is positive: $P(\prod_{i \in \iota}\overline{A_i}) > 0$.
--
--   The local lemma finds objects that avoid every one of many bad events even when those objects are exceedingly rare, provided each bad event depends on only a few others. It is the source of lower bounds such as $R(3, n) \ge c\, n^2/\ln^2 n$ (Section 16.8).
--
--   **Formalization Note.** The probability space is a `Fintype Ω` with the discrete σ-algebra and a probability measure `μ`, so every subset is an event, matching the book's finite probability spaces (p. 214). Probabilities are `μ.real`. The family is `A : ι → Set Ω` with `ι` finite, so repeated events are allowed. $N(i)$ is `N i : Finset ι` with `i ∉ N i`. Independence is `IndepOutside μ A N i`, the book's conditional equation in multiplicative form; see that definition. The two conclusions are stated as a conjunction. For empty `ι` the second conjunct says the whole space has positive probability.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 326–327, Lemma 16.14

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_IndepOutside

namespace AppliedComb.ManyFaces

open MeasureTheory

/-- Lemma 16.14, the Lovász Local Lemma, asymmetric form (Keller & Trotter, *Applied
Combinatorics* (2017 Edition), pp. 326–327). `(Ω, μ)` is a finite probability space in which every
subset is an event; the family `𝓕` is `A : ι → Set Ω` indexed by a finite type `ι`, and
`𝓝(A i) = N i ⊆ ι \ {i}`. If each `A i` is independent of any event not in `𝓝(A i)` and there are
reals `0 < x i < 1` with `P(A i) ≤ x i · ∏_{j ∈ N i} (1 − x j)`, then for every non-empty
subfamily `G`, `P(∏_{i ∈ G} Ā_i) ≥ ∏_{i ∈ G} (1 − x i)`; in particular the probability that all
events of the family fail is positive. -/
theorem local_lemma_asymmetric {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (N : ι → Finset ι) (hN : ∀ i, i ∉ N i)
    (hind : ∀ i, IndepOutside μ A N i) (x : ι → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    (∀ G : Finset ι, G.Nonempty → ∏ i ∈ G, (1 - x i) ≤ μ.real (allFail A G)) ∧
      0 < μ.real (allFail A Finset.univ) := by sorry

end AppliedComb.ManyFaces
