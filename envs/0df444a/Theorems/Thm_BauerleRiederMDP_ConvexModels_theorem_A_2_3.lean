-- Prove2me | Theorems.Thm_BauerleRiederMDP_ConvexModels_theorem_A_2_3
-- name    : BauerleRiederMDP.ConvexModels.theorem_A_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:22:51.165314+00:00
-- url     : https://prove2.me/theorems/586648fb-595f-4e9a-9f2b-68a69e523288
-- title:
--   Theorem A.2.3 (Selection Theorem) — a compact-valued map with Borel graph has a Borel selector
-- statement:
--   Let $E$ and $A$ be Borel spaces and let $x\mapsto D(x)$ assign to every $x\in E$ a non-empty compact set $D(x)\subset A$. If the graph
--   $$
--   D=\{(x,a)\in E\times A\mid a\in D(x)\}
--   $$
--   is a Borel subset of $E\times A$, then there is a Borel measurable $f:E\to A$ with $f(x)\in D(x)$ for all $x\in E$.
--
--   This is the selection theorem of Kuratowski and Ryll-Nardzewski, cited in the book; it yields measurable maximizers, in particular the bang-bang maximizer of Proposition 2.4.21.
--
--   **Formalization Note** A Borel space is encoded by a separable metrizable topology whose Borel σ-algebra is standard Borel, as in the platform's `MDPFinance.Semicontinuous` items.
--
--   Differences from the source:
--   - encoding: $E$, $A$ Borel spaces (Borel subsets of Polish spaces, Remark 2.1.2 a)) → `MetrizableSpace`, `SecondCountableTopology`, `BorelSpace`, `StandardBorelSpace`; reason: a Borel subset of a Polish space with the relative topology is separable metrizable with standard Borel σ-algebra, and conversely such a space embeds as a Borel subset of its completion
--   - encoding: 'a set-valued mapping ... D(x) is a non-empty subset of A' (p.351) → hypothesis $D(x)$ nonempty; reason: non-emptiness is part of the book's definition of a set-valued mapping
--   - encoding: $D$ a Borel subset of $E\times A$ → `MeasurableSet` for the product σ-algebra on `E × A`; reason: for second-countable $E$, $A$ the Borel σ-algebra of the product equals the product of the Borel σ-algebras; same instances
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem A.2.3, p.352 (PDF p.358); set-valued mappings p.351 (PDF p.357)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.ConvexModels

/-- **Theorem A.2.3 (Selection Theorem)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem A.2.3, p.352, PDF p.358; Kuratowski and
Ryll-Nardzewski (1965)). Let `E` and `A` be Borel spaces and let `x ↦ D(x)` be a
compact-valued set-valued mapping (so `D(x)` is a non-empty compact subset of `A` for every
`x`, p.351) whose graph `D := {(x, a) ∈ E × A | a ∈ D(x)}` is a Borel subset of `E × A`.
Then there exists a Borel measurable selector `f` for `D`: a Borel measurable `f : E → A`
with `f(x) ∈ D(x)` for all `x ∈ E`.

**Formalization Note.** A Borel space (Remark 2.1.2 a), p.14; p.351) is a Borel subset of a
Polish space with its relative topology and Borel σ-algebra. It is encoded, as in the
platform's `MDPFinance.Semicontinuous` items, by a separable metrizable topology
(`MetrizableSpace`, `SecondCountableTopology`) whose Borel σ-algebra (`BorelSpace`) is
standard Borel (`StandardBorelSpace`). Non-emptiness of `D(x)` is part of the book's
definition of a set-valued mapping (p.351). The σ-algebra on `E × A` is the product
σ-algebra, which is the Borel σ-algebra of the product here. -/
theorem theorem_A_2_3 {E A : Type*}
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (D : E → Set A) (hD_ne : ∀ x, (D x).Nonempty) (hD_cpt : ∀ x, IsCompact (D x))
    (hD_graph : MeasurableSet {p : E × A | p.2 ∈ D p.1}) :
    ∃ f : E → A, Measurable f ∧ ∀ x, f x ∈ D x := by sorry

end BauerleRiederMDP.ConvexModels
