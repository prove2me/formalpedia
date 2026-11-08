-- Prove2me | Theorems.Thm_DecrNbhdCover_claim_3_13
-- name    : DecrNbhdCover.claim_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:53.837599+00:00
-- url     : https://prove2.me/theorems/51b93a61-0535-4d8a-87f2-ae050862a808
-- title:
--   Claim 3.13 — MaintainSubgraphs: time $\tilde O(nN\mu)$
-- statement:
--   There is a deterministic algorithm for the MaintainSubgraphs problem with total update time
--   $$\tilde O(n\cdot N\cdot\mu),$$
--   where $n$ is the number of vertices of the initial graph $G$, and $N$ bounds the largest number of clusters of $\mathcal C$ that a single vertex of $G$ may ever lie in.
--
--   This bookkeeping lets every subroutine work on $G[C]$ and $H_C$.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word}+N)\rceil$; reason: the input words and the cluster numbers must fit
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: at all times, for a dynamic $G$ and $H$ and changes to the collection → each step is nonempty, has at most one update of $G$ and any updates of $H$ and changes to the collection, and the promise holds after each step; reason: p.16 indexes $G^{(\tau)},H^{(\tau)}$ by the updates of $G$; $H$-only steps occur when the problem runs on $G[C]$ and $H_C$ (§7)
--   - encoding: "maintain … the graphs $G[C]$ and $H_C$" → a reported change log of their edge sets, one edge per report, equal to the true sets after every step; reason: a change is a write, so it costs the same; $H_C$ is determined by its edges and $C$
--   - reading: new clusters → nonempty, with no repeated vertex; reason: an empty cluster contains no vertex, so $N$ would not bound the number of insertions
--   - encoding: $\mu>0$ real, $N$ a bound → $\mu$ a positive integer, $N\ge1$; reason: degrees are integers, and the printed bound would be $0$ at $N=0$
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Claim 3.13, p.20 (PDF 24); Definition 3.12, p.20 (PDF 24)

import Mathlib
import Definitions.Def_DecrNbhdCover_MaintainSubgraphs

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Claim 3.13.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.20 (PDF 24).

"There is a deterministic algorithm for the MaintainSubgraphs problem, whose total update time is Õ(n · N · µ), where n is the number of vertices in the initial graph G, and N bounds the largest number of clusters in C that a single vertex of G may ever lie in."

**Formalization Note.** `N` is a bound on the stream, not an input of the program. `N ≥ 1`, since the printed bound is `0` at `N = 0`. -/
theorem claim_3_13 :
    ∃ (C c₀ : ℕ) (P : Program), NoRand P ∧
      ∀ I : SubgraphInput, I.Ok →
        ∀ (eps : ℝ) (d : ℕ) (D : ℝ) (N W : ℕ) (σ : List SubgraphOp),
          0 < eps → eps < 1 → 0 < d → (d : ℝ) ≤ D → 1 ≤ N →
          c₀ * Nat.clog 2 (2 + subgraphProtocol.inputMax I.words σ + N) ≤ W →
          I.Promise eps d D N σ → SubgraphHolds C W P I N σ := by sorry

end DecrNbhdCover
