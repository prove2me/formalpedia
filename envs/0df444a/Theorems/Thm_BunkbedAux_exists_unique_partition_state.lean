-- Prove2me | Theorems.Thm_BunkbedAux_exists_unique_partition_state
-- name    : BunkbedAux.exists_unique_partition_state
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:58:11.28938+00:00
-- url     : https://prove2.me/theorems/1220ff7d-589b-44f3-8e33-63838982b95a
-- title:
--   Exactly one of the five partition events holds
-- statement:
--   The five partition probabilities $P_{abc}$, $P_{ab|c}$, $P_{ac|b}$, $P_{a|bc}$, $P_{a|b|c}$ of a triple of vertices are defined as the probabilities of five events describing which pairs among $a, b, c$ are connected in a percolation configuration. For those five numbers to be a probability distribution on the five Wierman--Ziff states — which is what the robustness lemma requires of them — the five events must partition the configuration space.
--
--   This theorem establishes exactly that: for every configuration $S$ and every triple $a, b, c$, **precisely one** of the five events holds.
--
--   The five events are, writing $\sim$ for connectivity in the configuration:
--   $$abc:\ a \sim b \wedge b \sim c; \qquad ab|c:\ a \sim b \wedge \neg(a \sim c); \qquad ac|b:\ a \sim c \wedge \neg(a \sim b);$$
--   $$a|bc:\ b \sim c \wedge \neg(a \sim b); \qquad a|b|c:\ \neg(a\sim b) \wedge \neg(b \sim c) \wedge \neg(a \sim c).$$
--
--   That these are exhaustive and mutually exclusive is not a formality — it rests on connectivity being an *equivalence* relation. There are exactly five partitions of $\{a,b,c\}$ into connectivity classes (all together, all separate, and the three ways of pairing two of them), and one has to check that the five conditions above, as written, pick out those five partitions one-to-one. For instance $abc$ is stated as $a \sim b \wedge b \sim c$ and captures the all-together case only because transitivity then forces $a \sim c$.
--
--   **Mathematical role.** This licenses treating a hyperedge gadget as a five-state random object: each configuration determines a unique state, so the percolation measure pushes forward to a genuine distribution on the five states, whose weights are precisely the five partition probabilities. That is what allows a gadget to be substituted for a hyperedge in a Wierman--Ziff model.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), where a gadget graph is substituted for each hyperedge.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **Exactly one of the five partition events holds.** For any configuration and any three
vertices, precisely one of the five mutually exclusive patterns -- all three connected, all three
separate, or exactly one of the three pairs joined -- occurs. -/
theorem exists_unique_partition_state {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (a b c : V) :
    ∃! s : WZ,
      (match s with
        | WZ.abc   => (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c
        | WZ.ab_c  => (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c
        | WZ.ac_b  => (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b
        | WZ.a_bc  => (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b
        | WZ.a_b_c => ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c
                        ∧ ¬ (ofEdges S).Reachable a c) := by
  sorry

end BunkbedAux
