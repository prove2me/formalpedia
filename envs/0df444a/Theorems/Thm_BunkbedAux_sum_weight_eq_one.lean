-- Prove2me | Theorems.Thm_BunkbedAux_sum_weight_eq_one
-- name    : BunkbedAux.sum_weight_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T18:37:43.334283+00:00
-- url     : https://prove2.me/theorems/82092d6a-e4d3-4f4c-85eb-961eb799cc26
-- title:
--   Total mass of the percolation measure is $1$
-- statement:
--   For a finite edge set $E$ and any weight function $w : E \to \mathbb{Q}$, the Bernoulli bond percolation measure has total mass one:
--
--   $$\sum_{S \subseteq E} \Bigl(\prod_{e \in S} w(e)\Bigr)\Bigl(\prod_{e \in E \setminus S} \bigl(1 - w(e)\bigr)\Bigr) \;=\; 1.$$
--
--   This is the binomial expansion of $\prod_{e \in E}\bigl(w(e) + (1 - w(e))\bigr)$, each factor of which is $1$. It is what makes every `probOf` quantity a genuine probability, and it is the normalisation that lets one eliminate the fifth of five partition probabilities in favour of the other four.
--
--   Note that no positivity or boundedness assumption on $w$ is needed: the identity is purely algebraic and holds for an arbitrary rational-valued weight, even one outside $[0,1]$ where the individual terms are not probabilities.
--
--   **Formalization Note** The statement is about `∑ S ∈ E.powerset, weight E w S`, with `weight` as given by the `BunkbedPercolation` definition. It follows from Mathlib's `Finset.prod_add`, which expands a product of sums over a `Finset` into a sum over its powerset of exactly this shape.
-- source:
--   Auxiliary identity for Bernoulli bond percolation as defined by the platform definition BunkbedPercolation. Standard measure-theoretic bookkeeping (total mass; exhaustive partition of a triple by its component structure; splitting a connection event by a third vertex), contributed as reusable infrastructure for the mission The Bunkbed Conjecture is False (N. Gladkov, I. Pak, A. Zimin, PNAS 122 (2025) e2420725122), where they underpin Proposition 5.4 on p. 8.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- The percolation measure on a finite edge set has total mass `1`. -/
theorem sum_weight_eq_one {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) : ∑ S ∈ E.powerset, weight E w S = 1 := by sorry

end BunkbedAux
