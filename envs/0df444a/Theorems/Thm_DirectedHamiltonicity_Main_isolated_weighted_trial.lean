-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_isolated_weighted_trial
-- name    : DirectedHamiltonicity.Main.isolated_weighted_trial
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:51:03.990404+00:00
-- url     : https://prove2.me/theorems/1cabb078-d037-5afe-992d-47e3a8017580
-- title:
--   A finite random arc-copy and isolation trial produces an odd weighted coefficient
-- statement:
--   Let a loopless $n$-vertex directed graph have a Hamiltonian path from $s$ to $t$, where $s\ne t$, no arc enters $s$, and no arc leaves $t$. For each arc independently sample a symbol uniform on 50 values. One value produces the empty subset of three incoming groups, and seven values produce each nonempty subset. Put one labelled copy in each chosen group. Independently give the $N=3(n-1)$ vertex-group pairs uniform integer weights in $\{1,\ldots,2N\}$.
--
--   With probability at least $\tfrac12(49/50)^{n-1}$, some total weight $B\le 2N(n-1)$ has an odd number of Hamiltonian paths in the copied multigraph.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_IsolationTrial

open DirectedHamiltonicity.Main

open Classical in
theorem DirectedHamiltonicity.Main.isolated_weighted_trial {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (s t : V) (hst : s ≠ t)
    (hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s) (ht : ∀ v, ¬ adj t v)
    (hp : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1/2 : ℝ) * (49/50 : ℝ)^(Fintype.card V-1) ≤
      ((Finset.univ.filter (IsolationTrial.Hits adj s t hs)).card : ℝ) /
        Fintype.card (IsolationTrial.Seed adj s) := by sorry
