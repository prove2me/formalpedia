-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_29
-- name    : DecrNbhdCover.theorem_3_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:34.173426+00:00
-- url     : https://prove2.me/theorems/a779af66-6209-4f64-bd7e-9d2cd4fe3130
-- title:
--   Theorem 3.29 — deterministic decremental neighborhood cover (corrected: $\max(1,m)$ in the sparsity bound)
-- statement:
--   There are universal constants $C,c_0$ and one deterministic program such that the following holds. The input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$, undergoing an online sequence of edge deletions, and parameters $0<\epsilon<1$, $D>0$. The program maintains a collection $\mathcal C$ of clusters of vertices of $G$ with these properties.
--
--   1. For every vertex $v$, the number of clusters that $v$ ever belongs to is at most $\min\{n^{C\epsilon},\max(1,m)^{C\epsilon}\}\cdot2^{C/\epsilon^C}$.
--   2. For every cluster and every pair $v,v'$ of its vertices, at all times, $\mathrm{dist}_G(v,v')\le2^{C/\epsilon^C}\cdot D$.
--   3. At all times, for every vertex $v$, the reported $\mathrm{CoveringCluster}(v)$ is a current cluster with $B_G(v,D)\subseteq\mathrm{CoveringCluster}(v)$.
--   4. After initialization, $\mathcal C$ changes only by vertex deletions from clusters and by new clusters, and all of these are reported.
--   5. A short-path query $(C,v,v')$, for $v,v'\in C\in\mathcal C$, returns a $v$-$v'$ path $P$ in $G$ of length at most $2^{C/\epsilon^C}\cdot D$, in $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--   6. The total update time is at most
--   $$C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right).$$
--
--   This is the paper's neighborhood cover theorem, the full version of its Theorem 1.1, and the input to its fully dynamic all-pairs shortest paths result (Theorem 10.4).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+n+m+L+\text{the numerators and denominators of }\epsilon,D)\rceil+\lceil(1/\epsilon)^{c_0}\rceil$, $L$ the largest edge length; reason: edge lengths and $D$ must fit in $O(1)$ words, since the bound has no $\log L$; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - correction: $\min\{n^{O(\epsilon)},m^{O(\epsilon)}\}\cdot2^{1/\mathrm{poly}(\epsilon)}$ in the sparsity bound → $\min\{n^{C\epsilon},\max(1,m)^{C\epsilon}\}\cdot2^{C/\epsilon^C}$; reason: with the explicit form of p.81 the bound is $0$ at $m=0$; counterexample meeting every assumption: one vertex, no edge, any $0<\epsilon<1$, $D>0$, where the third bullet needs a cluster containing $v$. C.11 handles isolated vertices by the cluster $\{v\}$
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: real $\epsilon$ and $D$ → rational $\epsilon$ and $D$ given by numerator and denominator; reason: a machine reads words; a real $\epsilon$ reduces to a rational in $[\epsilon/2,\epsilon]$ and a real $D$ to one in $[D,2D]$, with the factor $2$ absorbed by the constants, since integer lengths make the $D$-ball monotone in $D$
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → constants $C,c_0$ chosen before every graph and every $\epsilon$: $n^{C\epsilon}$, $2^{C/\epsilon^C}$ and $C(\log_2(2+n+m))^C$; reason: p.81: "there is a universal constant $C\ge1$", with this explicit form, and p.13 for $\tilde O$
--   - encoding: "maintains a pointer" and "reports" → $\mathrm{CoveringCluster}(v)$ and the updates of $\mathcal C$ are words of a report log folded into a state, in which an id is never reused and an illegal report makes the run fail; reason: a pointer change is a write, so the time is unchanged up to a constant, and no memory layout is fixed
--   - encoding: $n$-vertex graph, and query time $\tilde O(|E(P)|)$ → $n\ge1$, and $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: an empty vertex set has nothing to state, and C.11 returns a one-vertex path for $v=v'$
--   - encoding: "total update time" → the steps outside query windows, initialization included, where a window runs from the read of an operation to the read of the next one; reason: a query never changes the graph, and each query window has its own bound
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.29, p.29 (PDF 33); explicit bounds p.81 (PDF 85); proof C.11, pp.114–117 (PDF 118–121)

import Mathlib
import Definitions.Def_DecrNbhdCover_NeighborhoodCover

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.29 (Neighborhood cover in decremental graphs).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.29 (PDF 33).

"There is a deterministic algorithm that receives as input an n-vertex and m-edge graph G with integral lengths ℓG(e) > 0 on its edges e ∈ E(G), that undergoes an online sequence of edge deletions, and parameters 0 < ϵ < 1 and D > 0. The algorithm maintains a collection C of subsets of vertices of G called clusters with the following properties: for every vertex v ∈ V(G), the total number of clusters of C that v ever belongs to is bounded by min{n^O(ϵ), m^O(ϵ)} · 2^(1/poly(ϵ)); for every cluster C ∈ C, for every pair v, v′ ∈ C of its vertices, distG(v, v′) ≤ 2^(1/poly(ϵ)) · D; and for every vertex v ∈ V(G), at all times there is a cluster C = CoveringCluster(v) with BG(v, D) ⊆ C; the algorithm explicitly maintains, for every vertex v ∈ V(G), a pointer to the cluster CoveringCluster(v) with this property. Once the collection C of clusters is initialized, the only updates it undergoes are (i) deletion of vertices from clusters in C; and (ii) insertion of new clusters into C. The algorithm explicitly reports every vertex deletion from an existing cluster, and, whenever a new cluster C is inserted into C, it reports all vertices of C. Finally, the algorithm supports short-path queries: given a cluster C ∈ C and a pair v, v′ ∈ C of its vertices, return a v-v′ path P in G of length at most 2^(1/poly(ϵ)) · D, in time Õ(|E(P)|). The total update time of the algorithm is O(n + m^(1+O(ϵ)) · 2^(O(1/poly(ϵ))))."

**Formalization Note.** `C` and `c₀` are chosen before every graph and every `ϵ`, as p.81 makes explicit: "there is a universal constant C ≥ 1, such that … every vertex belongs to at most (m′)^(Cˆϵ) · 2^(C/ˆϵ^C) clusters …, the paths returned … have length at most 2^(C/ˆϵ^C) · D, and the total update time is at most C · (n′ + (m′)^(1+Cˆϵ) · 2^(C/ˆϵ^C))". The word size `W` is every value at least `c₀·⌈log₂(2 + n + m + L + the numerators and denominators of ϵ, D)⌉ + ⌈(1/ϵ)^c₀⌉`: the second term because the time budget contains `2^(C/ϵ^C)`, and a RAM addresses only `2^W` cells. `m^(O(ϵ))` is read as `max(1, m)^(Cϵ)` in the sparsity clause: at `m = 0` the printed bound is `0`, while a one-vertex edgeless graph needs a cluster containing its vertex. -/
theorem theorem_3_29 :
    ∃ (C c₀ : ℕ) (P : Program), NoRand P ∧
      ∀ I : GoalInput, I.Ok →
        ∀ W : ℕ, c₀ * I.logSize + ⌈(1 / (I.eps : ℝ)) ^ c₀⌉₊ ≤ W →
          ∀ σ : List GOp, I.Valid W P σ → GoalHolds C W P I σ := by sorry

end DecrNbhdCover
