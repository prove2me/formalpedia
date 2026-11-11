-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_2_6
-- name    : ExactAutobid.Equilibria.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:56.800181+00:00
-- url     : https://prove2.me/theorems/a6b1c2b2-2ac4-4565-b5ae-f14d192b82ad
-- title:
--   Lemma 2.6 — bounding gate outdegree by complement copies, with a bijection of solution sets
-- statement:
--   Let $G$ be a gate network whose gates have indegree at most $d$, and let $C(x) = 1-x$ be the complement gate. Then $G$ admits an **expansion** $G'$, obtained by adding complement gates, such that $G'$ has at most $K\cdot N$ variables for a constant $K$ depending only on $d$, every variable of $G'$ has **outdegree at most two**, no gate of $G'$ reads its own output, and restriction to the original variables is a bijection
--   $$\mathrm{Sol}(G') \to \mathrm{Sol}(G),\qquad x' \mapsto x' \circ e,$$
--   where $e$ embeds the original variables into $G'$.
--
--   The lemma lets every wire bidder of the auction reductions serve a bounded number of downstream gadgets, which is what gives the constant bounds on goods per bidder.
--
--   Differences from the source:
--   - reading: a bounded-indegree gate network admits a linear-size expansion → for every indegree bound d there is K such that every network G with indegree ≤ d has an expansion G' with G'.N ≤ K · G.N; reason: 'bounded' and 'linear-size' quantified as constants fixed before the network
--   - reading: expansion with complement gates → every gate of G' is a complement gate or has the type of some gate of G, and the original variables embed into G' by an injection e; reason: what 'expansion' means in the proof: original gates kept, complement copies added
--   - encoding: gates x_i = f(x_j, x_k) or unary, variables in [0,1] → gate types as (arity, relation) pairs; solutions are assignments in [0,1]^N satisfying every relation; reason: Lean convention covering any gate set
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 6 (PDF 8), Lemma 2.6

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_Circuits

namespace ExactAutobid.Equilibria

/-- **Lemma 2.6 (Bounding Gate Outdegree).** For every indegree bound `d` there is a constant `K`
such that every gate network with indegree at most `d` has an expansion, by complement gates, with
at most `K · N` variables, outdegree at most two and no self-loops, in which restriction to the
original variables is a bijection between the expanded and the original solution sets. -/
theorem lemma_2_6 (d : ℕ) : ∃ K : ℕ, ∀ G : GateNetwork, (∀ i, (G.gate i).type.arity ≤ d) →
    ∃ (G' : GateNetwork) (e : Fin G.N ↪ Fin G'.N),
      G'.N ≤ K * G.N ∧
      (∀ i, (G'.gate i).type = complGate ∨ ∃ j, (G'.gate i).type = (G.gate j).type) ∧
      (∀ v, G'.outdeg v ≤ 2) ∧ G'.NoSelfLoops ∧
      Set.BijOn (fun x' : Fin G'.N → ℝ => x' ∘ e) G'.Sol G.Sol := by sorry

end ExactAutobid.Equilibria
