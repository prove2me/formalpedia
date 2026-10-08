-- Prove2me | Theorems.Thm_ConstrNestedLogit_Card_eq_8
-- name    : ConstrNestedLogit.Card.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:32.611886+00:00
-- url     : https://prove2.me/theorems/b1eafc75-c0dc-4b5b-8b43-6495ae97cbcf
-- title:
--   (8), p. 15 — the objective of problem (7) is linear: $V_i(S)(R_i(S)-u)=\sum_{j\in S} v_{ij}(r_{ij}-u)$
-- statement:
--   Let $i$ be a nest of a nested logit instance in which a customer who chooses the nest always buys (no within-nest no-purchase weight), so that $V_i(S) = \sum_{j \in S} v_{ij}$, and let the preference weights $v_{ij}$ of the nest be positive. Let $R_i(S) = \sum_{j\in S} v_{ij} r_{ij} / V_i(S)$, with $R_i(\emptyset) = 0$. Then for every assortment $S \subseteq N$ and every $u \in \mathbb{R}$,
--
--   $$V_i(S)\,\bigl(R_i(S) - u\bigr) = \sum_{j \in S} v_{ij}\,(r_{ij} - u).$$
--
--   This is the identity that makes problem (7) linear in the assortment, and it turns (7) under cardinality constraints into the unit-weight knapsack problem (9).
--
--   **Formalization Note** The published `V` includes a within-nest no-purchase weight `vnp i`, set to $0$ here, which is the paper's main model. Positivity of the $v_{ij}$ is not restated on the page but is part of the model ($v_{ij} = e^{\bar u_{ij}/\gamma_i}$, p. 10); it guarantees $V_i(S) \neq 0$ for $S \ne \emptyset$. The case $S = \emptyset$ holds through $R_i(\emptyset) = 0$. The identity is stated for every real $u$; the paper uses it for $u \ge 0$.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 15, eq. (8)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

open NestedLogitVariants.LP

namespace ConstrNestedLogit.Card

/-- Equation (8) (p. 15): with no within-nest no-purchase weight (`v_i0 = 0`, so
`V_i(S) = ∑_{j ∈ S} v_ij`) and positive preference weights, the objective of problem (7) is linear
in the assortment: `V_i(S)(R_i(S) − u) = ∑_{j ∈ S} v_ij (r_ij − u)`, including `S = ∅`. -/
theorem eq_8 {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) (S : Finset (Fin n)) (u : ℝ) :
    V I i S * (R I i S - u) = ∑ j ∈ S, I.v i j * (I.r i j - u) := by sorry

end ConstrNestedLogit.Card
