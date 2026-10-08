-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_lemma7_21_open_selector
-- name    : BertsekasShreve.SemicontSelection.lemma7_21_open_selector
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:56.246466+00:00
-- url     : https://prove2.me/theorems/0d1813db-ff76-4a5a-bdd6-025c7d1ab568
-- title:
--   Lemma 7.21 — an open subset of $XY$ has an open projection and a Borel-measurable selector
-- statement:
--   Let $X$ be a metrizable space, $Y$ a separable metrizable space, and $G$ an open subset of $X\times Y$. Then the projection
--
--   $$\operatorname{proj}_X(G)=\{x\in X\mid (x,y)\in G\text{ for some }y\in Y\}$$
--
--   is open in $X$, and there is a Borel-measurable function $\varphi:\operatorname{proj}_X(G)\to Y$ whose graph lies in $G$:
--
--   $$(x,\varphi(x))\in G\qquad\forall x\in\operatorname{proj}_X(G).$$
--
--   This is the selection step for the upper semicontinuous case, used to build the $\varepsilon$-optimal selectors of Proposition 7.34.
--
--   **Formalization Note** $\operatorname{proj}_X(G)$ is `Prod.fst '' G`; $\varphi$ is defined on that subtype, which carries the Borel σ-algebra of its subspace topology.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 154, Lemma 7.21

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.21 (Bertsekas & Shreve, p. 154). Let `X` be metrizable, `Y` separable metrizable and
`G ⊆ X × Y` open. Then `proj_X(G)` is open and there is a Borel-measurable
`φ : proj_X(G) → Y` with `Gr(φ) ⊆ G`, i.e. `(x, φ(x)) ∈ G` for every `x ∈ proj_X(G)`. -/
theorem lemma7_21_open_selector {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (G : Set (X × Y)) (hG : IsOpen G) :
    IsOpen (Prod.fst '' G) ∧
      ∃ φ : (Prod.fst '' G) → Y, Measurable φ ∧ ∀ x : (Prod.fst '' G), ((x : X), φ x) ∈ G := by sorry

end BertsekasShreve.SemicontSelection
