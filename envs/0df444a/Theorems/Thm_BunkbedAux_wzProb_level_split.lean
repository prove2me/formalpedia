-- Prove2me | Theorems.Thm_BunkbedAux_wzProb_level_split
-- name    : BunkbedAux.wzProb_level_split
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T00:33:55.692443+00:00
-- url     : https://prove2.me/theorems/9c5b6470-68af-4f3b-8270-65e9e8c3756e
-- title:
--   Splitting a Wierman--Ziff configuration into its two levels
-- statement:
--   In the Wierman--Ziff model on a hypergraph with edge set indexed by $\iota$, a configuration assigns one of five states to each hyperedge *on each of the two levels* of the bunkbed. Formally it is a function on $\iota \times \{0,1\}$, and $\texttt{wzProb}$ is defined as a sum over all such functions, weighted by the product of the state probabilities.
--
--   This lemma records the elementary but useful observation that a function on $\iota \times \{0,1\}$ is the same thing as a **pair** of functions on $\iota$ — one describing the lower level, one the upper — and that the configuration weight factors correspondingly:
--
--   $$\mathbb{P}^{\mathrm{wz}}[x \leftrightarrow y] \;=\; \sum_{(c_0,\,c_1)} \mathbf{1}\bigl[x \leftrightarrow y \text{ in the graph glued from } c_0, c_1\bigr]\;\Bigl(\prod_{i} P(c_0(i))\Bigr)\Bigl(\prod_{i} P(c_1(i))\Bigr),$$
--
--   the sum running over all pairs of level configurations $c_0, c_1 : \iota \to \Upsilon$, where $\Upsilon$ is the five-element state space.
--
--   The statement holds for an arbitrary index type, vertex type, hypergraph, transversal set, weight function and pair of endpoints; no hypothesis on $P$ is needed, and in particular $P$ need not be a probability distribution.
--
--   **Mathematical role.** This is the first step in any analysis of the Wierman--Ziff model that treats the two levels separately. The point is that the two levels are percolated independently, so once the sum is written this way the weight is a product of a level-$0$ factor and a level-$1$ factor, and only the connectivity indicator couples them. That is what makes it possible to group configurations by the partition of the vertex set that each level induces — the reduction underlying the evaluation of the difference of the two connection probabilities on Hollom's hypergraph.
--
--   **Formalization note.** The gluing map sends a pair $(c_0, c_1)$ to the configuration taking the value $c_0(i)$ at $(i,0)$ and $c_1(i)$ at $(i,1)$; it is a bijection, and the product over $\iota \times \{0,1\}$ splits into the two level products.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.2 (p. 3), where the Wierman-Ziff model is introduced with the two levels percolated independently.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **Splitting a Wierman-Ziff configuration into its two levels.** A WZ configuration assigns a
state to each hyperedge on each of the two levels, i.e. it is a function on `ι × Fin 2`. Such a
function is the same thing as a pair of functions on `ι`, one per level, and the configuration
weight factors accordingly. This rewrites `wzProb` as a double sum over the two level
configurations. -/
theorem wzProb_level_split {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (P : WZ → ℚ) (x y : V × Fin 2) :
    wzProb t T P x y
      = ∑ c : (ι → WZ) × (ι → WZ),
          (if (wzGraph t T (fun p => if p.2 = 0 then c.1 p.1 else c.2 p.1)).Reachable x y
            then (1 : ℚ) else 0) * ((∏ i, P (c.1 i)) * (∏ i, P (c.2 i))) := by
  sorry

end BunkbedAux
