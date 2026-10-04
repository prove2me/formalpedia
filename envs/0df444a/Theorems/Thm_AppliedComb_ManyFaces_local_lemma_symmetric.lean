-- Prove2me | Theorems.Thm_AppliedComb_ManyFaces_local_lemma_symmetric
-- name    : AppliedComb.ManyFaces.local_lemma_symmetric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:56:39.851803+00:00
-- url     : https://prove2.me/theorems/aa2a6df0-69ec-4547-aa23-58a37a732353
-- title:
--   Lemma 16.15 — the Lovász Local Lemma, symmetric form
-- statement:
--   Let $(\Omega, P)$ be a finite probability space and $\mathcal F = (A_i)_{i \in \iota}$ a finite family of events. For each $i$ let $N(i) \subseteq \iota \setminus \{i\}$ be a subfamily such that $A_i$ is independent of any event not in $N(i)$, that is, $P(A_i \cap \prod_{j \in G}\overline{A_j}) = P(A_i)\,P(\prod_{j \in G}\overline{A_j})$ for every $G \subseteq \iota$ with $i \notin G$ and $G \cap N(i) = \emptyset$. Let $p$ and $d$ be real numbers with $0 < p < 1$ and $d \ge 1$, and suppose that
--   $$P(A_i) \le p, \qquad |N(i)| \le d \quad \text{for every } i, \qquad e\,p\,(d+1) < 1,$$
--   where $e$ is the base of the natural logarithm. Then
--   $$P\Big(\prod_{i \in \iota} \overline{A_i}\Big) \;\ge\; \Big(1 - \frac{1}{d+1}\Big)^{|\mathcal F|} \;>\; 0,$$
--   so the probability that all events of $\mathcal F$ fail is positive.
--
--   This is the form in which the local lemma is usually applied: it needs only a uniform bound on the probabilities and on the number of dependencies.
--
--   **Formalization Note.** The page's displayed conclusion, $P(\prod_{E\in\mathcal F}\overline E) \ge \prod_{E\in\mathcal G}(1 - x(E))$, mentions $\mathcal G$ and $x$, which the lemma never introduces, and its gloss reads "the probability that all events in $\mathcal F$ is positive". The book's proof sets $x(E) = 1/(d+1)$ and applies Lemma 16.14 with $\mathcal G = \mathcal F$; the statement is that reading: the explicit bound $(1 - 1/(d+1))^{|\mathcal F|}$, with $|\mathcal F| = $ `Fintype.card ι`, together with positivity. The probability space is a `Fintype Ω` with the discrete σ-algebra and a probability measure `μ`, so every subset is an event, as in the book's definition (p. 214). The family is indexed by a finite type `ι` (repetitions allowed), and `N i` is a `Finset ι` with `i ∉ N i`. The independence hypothesis is `IndepOutside`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 328, Lemma 16.15 (conclusion misprinted; read from the proof, x(E) = 1/(d+1))

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_IndepOutside

namespace AppliedComb.ManyFaces

open MeasureTheory

/-- Lemma 16.15, the Lovász Local Lemma, symmetric form (Keller & Trotter, *Applied
Combinatorics* (2017 Edition), p. 328). `(Ω, μ)` is a finite probability space, the family is
`A : ι → Set Ω` with `𝓝(A i) = N i ⊆ ι \ {i}` and each `A i` independent of any event not in
`𝓝(A i)`. If `0 < p < 1`, `d ≥ 1`, `P(A i) ≤ p` and `|N i| ≤ d` for every `i`, and
`e · p · (d + 1) < 1`, then the probability that all events of the family fail is positive.
The page's displayed conclusion is misprinted; with the choice `x(E) = 1/(d + 1)` made in the
book's proof it reads `P(∏_{i} Ā_i) ≥ (1 − 1/(d + 1))^{|𝓕|}`, which is stated together with the
positivity. -/
theorem local_lemma_symmetric {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p d : ℝ) (hp : 0 < p ∧ p < 1) (hd : 1 ≤ d)
    (A : ι → Set Ω) (N : ι → Finset ι) (hN : ∀ i, i ∉ N i)
    (hind : ∀ i, IndepOutside μ A N i)
    (hPp : ∀ i, μ.real (A i) ≤ p) (hNd : ∀ i, ((N i).card : ℝ) ≤ d)
    (he : Real.exp 1 * p * (d + 1) < 1) :
    (1 - 1 / (d + 1)) ^ Fintype.card ι ≤ μ.real (allFail A Finset.univ) ∧
      0 < μ.real (allFail A Finset.univ) := by sorry

end AppliedComb.ManyFaces
