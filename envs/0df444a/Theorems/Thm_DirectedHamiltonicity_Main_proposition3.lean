-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_proposition3
-- name    : DirectedHamiltonicity.Main.proposition3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:23.227294+00:00
-- url     : https://prove2.me/theorems/d0f269b6-8689-417c-8ee1-9fb511b74921
-- title:
--   Proposition 3 — with probability $\ge(1-\delta)^{n-1}$ some group selection has an odd number of Hamiltonian paths
-- statement:
--   Let $G=(V,A)$ be a simple loopless directed graph on $n$ vertices with distinct vertices $s,t$, no arcs entering $s$ and no arcs leaving $t$, and let $d\ge2$, $\delta=1/(1+(2^d-1)^2)$. Build $\widehat G$ from independent sets $S_{uv}\subseteq[d]$ with $\Pr[S_{uv}=\varnothing]=\delta$ and $\Pr[S_{uv}=S]=(1-\delta)/(2^d-1)$ for $S\ne\varnothing$, placing one copy of $uv$ in the incoming group $\widehat A_{v,\ell}$ for each $\ell\in S_{uv}$. If $G$ has a Hamiltonian path from $s$ to $t$, then with probability at least
--   $$(1-\delta)^{n-1}$$
--   there exists a tuple $(\ell_v)_{v\ne s}\in[d]^{n-1}$ such that the multigraph $\bigl(V,\bigcup_{v\ne s}\widehat A_{v,\ell_v}\bigr)$ has an odd number of Hamiltonian paths from $s$ to $t$.
--
--   The event is the existence of a good selection inside one sample of the copy sets, not the probability that a uniformly chosen selection is good. Combined with the isolation lemma this yields an odd parity at a single total weight, which Proposition 4 can detect.
--
--   Differences from the source:
--   - encoding: G = (V, A) a simple loopless directed graph on n vertices with distinct s, t, no arcs entering s and none leaving t, and d ≥ 2 (standing assumptions of §2, PDF p.4) → an adjacency relation adj on a finite type V with n = |V|, and the hypotheses s ≠ t, ∀ v, ¬adj v v, ∀ u, ¬adj u s, ∀ v, ¬adj t v, 2 ≤ d; reason: a simple digraph is exactly a relation; the standing assumptions are written as binders; [d] is Fin d
--   - encoding: probability over the independent random sets S_uv ⊆ [d] with Pr[S_uv = ∅] = δ and Pr[S_uv = S] = (1−δ)/(2^d−1) for S ≠ ∅ → copyProb d E = Σ over joint outcomes S satisfying E of ∏_{uv} copySetProb d (S uv); reason: the product law of finitely many independent finite random variables, written as an explicit finite sum
--   - encoding: a directed (multi)graph with arc set E(H); a Hamiltonian path from s to t as a path visiting every vertex once → Multidigraph V E (tail, head : E → V, arcs labelled by E); a Hamiltonian path is a sequence of n−1 arcs e_0,…,e_{n−2} with tail e_i = v_i, head e_i = v_{i+1}, v_0 = s, v_{n−1} = t, and v injective; reason: a bijection with the source paths; parallel copies of an arc give distinct paths, as in the source
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.4 / printed p.3, Proposition 3 (repeated PDF p.6 / printed p.5)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies

namespace DirectedHamiltonicity.Main

open Multidigraph

open Classical in
/-- Proposition 3, PDF p.4 / printed p.3 (repeated PDF p.6). Let `G` (adjacency `adj`) be a simple
loopless digraph on `n` vertices with distinct `s, t`, no arc entering `s` and no arc leaving `t`,
and let `d ≥ 2`. If `G` has a Hamiltonian path from `s` to `t`, then with probability at least
`(1 − δ)^{n−1}` over the random sets `S_uv`, there is a tuple `(ℓ_v)_{v ≠ s} ∈ [d]^{n−1}` such that
the multigraph `(V, ⋃_{v ≠ s} Â_{v,ℓ_v})` of the copies in the selected groups has an odd number of
Hamiltonian paths from `s` to `t`. -/
theorem proposition3 {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    [DecidableRel adj] (s t : V) (hst : s ≠ t) (hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s)
    (ht : ∀ v, ¬ adj t v) (d : ℕ) (hd : 2 ≤ d) (hham : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1 - delta d) ^ (Fintype.card V - 1) ≤
      copyProb (adj := adj) d (fun S => ∃ sel : {v // v ≠ s} → Fin d,
        Odd ((selectedGraph adj S s sel).hamPaths s t).card) := by sorry

end DirectedHamiltonicity.Main
