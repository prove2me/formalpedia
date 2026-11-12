-- Prove2me | Theorems.Thm_BunkbedAux_partition_sum_eq_total
-- name    : BunkbedAux.partition_sum_eq_total
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T18:38:12.242044+00:00
-- url     : https://prove2.me/theorems/997442b6-8ae7-44e5-aa9b-0d3acae55b1d
-- title:
--   The five partition probabilities of a triple exhaust the measure
-- statement:
--   Fix a finite edge set $E$, a weight function $w$, and three vertices $a, b, c$. In the percolation, the connected components induce a partition of $\{a,b,c\}$, and there are exactly five possibilities: all three together, one of the three pairs together with the third vertex apart, or all three separate. Writing $P_{abc}, P_{ab|c}, P_{ac|b}, P_{a|bc}, P_{a|b|c}$ for the probabilities of these five events,
--
--   $$P_{abc} + P_{ab|c} + P_{ac|b} + P_{a|bc} + P_{a|b|c} \;=\; \sum_{S \subseteq E} \mathrm{weight}(S).$$
--
--   The content is that the five events are mutually exclusive and exhaustive. This holds because reachability in any fixed open subgraph is an *equivalence relation*: the triple of truth values of $(a \leftrightarrow b,\; b \leftrightarrow c,\; a \leftrightarrow c)$ can therefore only be $(T,T,T)$, $(T,F,F)$, $(F,T,F)$, $(F,F,T)$ or $(F,F,F)$, and these five patterns correspond bijectively to the five quantities. The three patterns ruled out by transitivity — those with exactly two of the relations true — are precisely what makes the count five rather than eight.
--
--   Combined with the fact that the total mass is $1$, this gives the relation used to eliminate $P_{a|b|c}$ from any expression in the five, which is how the source converts its determinant-shaped quantity $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$ into connection probabilities.
--
--   **Formalization Note** The right-hand side is left as the total mass rather than $1$, so that this lemma is independent of the normalisation lemma and the two can be combined as needed. The five definitions in `BunkbedPercolation` are phrased asymmetrically — for instance $P_{a|bc}$ negates $a \leftrightarrow b$ while $P_{ac|b}$ also negates $a \leftrightarrow b$ — and they agree with the symmetric descriptions only via transitivity, which the proof must supply.
-- source:
--   Auxiliary identity for Bernoulli bond percolation as defined by the platform definition BunkbedPercolation. Standard measure-theoretic bookkeeping (total mass; exhaustive partition of a triple by its component structure; splitting a connection event by a third vertex), contributed as reusable infrastructure for the mission The Bunkbed Conjecture is False (N. Gladkov, I. Pak, A. Zimin, PNAS 122 (2025) e2420725122), where they underpin Proposition 5.4 on p. 8.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- The five partition probabilities of a triple exhaust the measure. -/
theorem partition_sum_eq_total {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pab_c E w a b c + Pac_b E w a b c + Pa_bc E w a b c + Pa_b_c E w a b c
      = ∑ S ∈ E.powerset, weight E w S := by sorry

end BunkbedAux
