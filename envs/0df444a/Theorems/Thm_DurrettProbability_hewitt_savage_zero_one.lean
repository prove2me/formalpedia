-- Prove2me | Theorems.Thm_DurrettProbability_hewitt_savage_zero_one
-- name    : DurrettProbability.hewitt_savage_zero_one
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:04:23.780795+00:00
-- url     : https://prove2.me/theorems/3c56d30f-f025-483f-80ba-f53bcfd438ef
-- title:
--   Theorem 2.5.4 — the Hewitt-Savage 0-1 law
-- statement:
--   Let $X_1,X_2,\dots$ be independent and identically distributed, realized as the coordinates of
--   the sequence space $S^{\mathbb{N}}$ under the infinite product of copies of one law. An event $A$
--   is **permutable** when rearranging finitely many coordinates does not change it: for every
--   bijection $\sigma$ of $\mathbb{N}$ fixing all but finitely many indices,
--   $\{\omega:\omega\circ\sigma\in A\}=A$. Then
--   $$\mathbb{P}(A)\in\{0,1\}.$$
--
--   This strengthens Kolmogorov's 0-1 law in the i.i.d. case. Every tail event is permutable, since a
--   permutation of the first $n$ coordinates cannot affect an event determined by the coordinates
--   beyond $n$; but the converse fails, and the standard witness is
--   $\{S_n\in B\text{ infinitely often}\}$, which is permutable — because $S_n(\omega)=S_n(\sigma\omega)$
--   for large $n$ — but not a tail event. So the exchangeable σ-field is strictly larger than the tail
--   σ-field, and the theorem says that for an i.i.d. sequence both are trivial.
--
--   The consequences are the useful part: for a random walk with i.i.d. steps, statements like
--   "$\limsup_n S_n/c_n\ge1$" or "the walk visits $B$ infinitely often" have probability $0$ or $1$,
--   with no further argument.
--
--   **Formalization Note** The sequence space is the countable product $\mathbb{N}\to S$ carrying the
--   infinite product measure, so "i.i.d." is built into the setting rather than hypothesised. A
--   permutable event is given by its invariance property directly; the fact that such events form a
--   σ-field is not needed for the statement and is not asserted.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 82 (PDF p. 90), Theorem 2.5.4: 'Hewitt-Savage 0-1 law. If X_1, X_2, ... are i.i.d. and A is in the exchangeable sigma-field E then P(A) is 0 or 1.' The definitions on the same page: 'A finite permutation of N = {1, 2, ...} is a map pi from N onto N so that pi(i) != i for only finitely many i. ... An event A is permutable if pi^{-1} A = {omega : pi omega in A} is equal to A for any finite permutation pi, or in other words, if its occurrence is not affected by rearranging finitely many of the random variables. The collection of permutable events is a sigma-field. It is called the exchangeable sigma-field and denoted by E.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem hewitt_savage_zero_one {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] (A : Set (ℕ → S)) (hA : IsPermutable A) :
    (Measure.infinitePi (fun _ : ℕ => μ)) A = 0
      ∨ (Measure.infinitePi (fun _ : ℕ => μ)) A = 1 := by sorry

end DurrettProbability
