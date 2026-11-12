-- Prove2me | Theorems.Thm_BunkbedAux_Pabc_add_Pab_c_eq_connProb
-- name    : BunkbedAux.Pabc_add_Pab_c_eq_connProb
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T18:38:14.297744+00:00
-- url     : https://prove2.me/theorems/d262d6a8-44ff-4ec9-a1c1-be2964d17644
-- title:
--   Splitting a connection probability by the status of a third vertex
-- statement:
--   Fix a finite edge set $E$, a weight function $w$, and three vertices $a, b, c$. Then
--
--   $$P_{abc} + P_{ab|c} \;=\; \mathbb{P}\bigl(a \leftrightarrow b\bigr).$$
--
--   In words: the event that $a$ and $b$ are connected splits into exactly two disjoint sub-events according to whether the third vertex $c$ joins them. The reason the split is exact is that, *given* $a \leftrightarrow b$, the relations $b \leftrightarrow c$ and $a \leftrightarrow c$ are equivalent, since reachability is transitive and symmetric; so the first sub-event is $P_{abc}$ and its complement within $\{a \leftrightarrow b\}$ is $P_{ab|c}$.
--
--   This identity is how partition probabilities of a triple are converted into ordinary two-point connection probabilities, which is what makes closed-form computations of the former possible: one computes $\mathbb{P}(a \leftrightarrow b)$ and $P_{abc}$ by other means and reads off $P_{ab|c}$ as the difference.
--
--   **Formalization Note** The definitions in `BunkbedPercolation` give $P_{abc}$ as the event $a \leftrightarrow b \wedge b \leftrightarrow c$ and $P_{ab|c}$ as $a \leftrightarrow b \wedge \neg(a \leftrightarrow c)$, so the proof is a pointwise case analysis over configurations, using transitivity to see that the two conditions are complementary under $a \leftrightarrow b$. Both sides are sums over `E.powerset`, so the sums can be merged before the pointwise argument.
-- source:
--   Auxiliary identity for Bernoulli bond percolation as defined by the platform definition BunkbedPercolation. Standard measure-theoretic bookkeeping (total mass; exhaustive partition of a triple by its component structure; splitting a connection event by a third vertex), contributed as reusable infrastructure for the mission The Bunkbed Conjecture is False (N. Gladkov, I. Pak, A. Zimin, PNAS 122 (2025) e2420725122), where they underpin Proposition 5.4 on p. 8.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- Splitting a two-point connection probability by the status of a third vertex. -/
theorem Pabc_add_Pab_c_eq_connProb {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pab_c E w a b c = connProb E w a b := by sorry

end BunkbedAux
