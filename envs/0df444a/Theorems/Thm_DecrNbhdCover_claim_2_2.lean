-- Prove2me | Theorems.Thm_DecrNbhdCover_claim_2_2
-- name    : DecrNbhdCover.claim_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:47.664514+00:00
-- url     : https://prove2.me/theorems/04c5ce42-8ad2-483f-a5fa-b2bd9d8e5c99
-- title:
--   Claim 2.2 — degree reduction: $|V(\tilde G)|=n+8m$, degree $O(\log\Lambda)$, distances within $1+\epsilon$, path translation, $\tilde O(m+n)$ time
-- statement:
--   There is a deterministic algorithm with the following input: $0<\epsilon<1$, $\Lambda$, and an $n$-vertex graph $G$ with $m\ge1$ edges initially and integer lengths $K\le\ell_G(e)\le\Lambda$, where $K=2\lceil64\log(2m)/\epsilon\rceil$, undergoing edge deletions. It maintains a dynamic graph $\tilde G$ with $V(G)\subseteq V(\tilde G)$, whose only updates after initialization are edge deletions, such that $|V(\tilde G)|=n+8m$, the maximum degree of $\tilde G$ is $O(\log\Lambda)$, all lengths are positive even integers, and at all times, for $u,v\in V(G)$,
--   $$\mathrm{dist}_G(u,v)\le\mathrm{dist}_{\tilde G}(u,v)\le(1+\epsilon)\mathrm{dist}_G(u,v).$$
--   A (possibly non-simple) path $\tilde P$ in $\tilde G$ between distinct $u,v\in V(G)$ is translated in time $O(|E(\tilde P)|)$ into a (possibly non-simple) $u$-$v$ path $P$ in $G$ with $\ell_G(P)\le\ell_{\tilde G}(\tilde P)$ and $|E(P)|\ge\Omega(\epsilon|E(\tilde P)|/\log(2m))$. A non-isolated vertex $u$ of $\tilde G$ is mapped in $O(1)$ time to a non-isolated vertex $v$ of $G$ with $\mathrm{dist}_{\tilde G}(u,v)\le\epsilon\Lambda$. The total update time is $\tilde O(m+n)$.
--
--   This reduction lets the later tools assume low degree and still return long enough paths in the original graph.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil$; reason: the input words must fit
--   - encoding: real $\epsilon$ and $\Lambda$ → rational $\epsilon$ and natural $\Lambda$; reason: a machine reads words; lengths are integers, so $\Lambda$ may be replaced by its floor
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - encoding: "there is a deterministic algorithm" three times → one program answering translation and vertex queries; reason: the claim uses them with the maintained $\tilde G$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Claim 2.2, p.15 (PDF 19)

import Mathlib
import Definitions.Def_DecrNbhdCover_DegreeReduction

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Claim 2.2.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.15 (PDF 19).

"There is a deterministic algorithm, whose input consists of 0 < ϵ < 1 and Λ, and an n-vertex graph G, that initially contains m ≥ 1 edges, and integral lengths K ≤ ℓG(e) ≤ Λ on its edges e ∈ E(G), where K = 2⌈64 log(2m)/ϵ⌉, such that G undergoes an online sequence of edge deletions. The algorithm maintains a dynamic graph G̃ with V(G) ⊆ V(G̃), such that, after initialization, the only updates that G̃ undergoes are edge deletions. The algorithm ensures that |V(G̃)| = n + 8m, that the maximum vertex degree in G̃ is at most O(log Λ), and that all edge lengths in G̃ are positive even integers. Additionally, for every pair u, v ∈ V(G), at all times, distG(u, v) ≤ dist_G̃(u, v) ≤ (1+ϵ)distG(u, v) holds. Moreover, there is a deterministic algorithm that, given a (possibly non-simple) path P̃ in G̃ connecting distinct vertices u, v ∈ V(G), computes, in time O(|E(P̃)|), a (possibly non-simple) u-v path P in G with ℓG(P) ≤ ℓ_G̃(P̃) and |E(P)| ≥ Ω(ϵ·|E(P̃)|/log(2m)). Lastly, there is a deterministic algorithm that, given a non-isolated vertex u of G̃, computes in O(1) time a non-isolated vertex v of G such that dist_G̃(u, v) ≤ ϵΛ (where, possibly, v = u). The total update time of the algorithm is Õ(m+n)."

**Formalization Note.** The three algorithms are one program, whose queries are the translation and vertex operations of `DegOp`. -/
theorem claim_2_2 :
    ∃ (C c₀ : ℕ) (P : Program), NoRand P ∧
      ∀ I : DegInput, I.Ok →
        ∀ (W : ℕ) (σ : List DegOp), c₀ * Nat.clog 2 (2 + degProtocol.inputMax I.words σ) ≤ W →
          I.Valid W P σ → DegHolds C W P I σ := by sorry

end DecrNbhdCover
