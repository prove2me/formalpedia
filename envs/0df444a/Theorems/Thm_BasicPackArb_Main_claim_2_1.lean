-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_1
-- name    : BasicPackArb.Main.claim_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:15.713505+00:00
-- url     : https://prove2.me/theorems/7365f8d1-f92e-4e0e-8b23-5b77097f857f
-- title:
--   Claim 2.1 — if $r_M$ is modular on $P,Q$ and $s$ is spanned by both, then $s$ is spanned by $P\cap Q$
-- statement:
--   Let $M$ be a matroid on a finite set $S$ with rank function $r_M$, let $P,Q\subseteq S$ satisfy
--   $$r_M(P\cap Q)+r_M(P\cup Q)=r_M(P)+r_M(Q),$$
--   and let $s\in\mathrm{Span}_M(P)\cap\mathrm{Span}_M(Q)$. Then $s\in\mathrm{Span}_M(P\cap Q)$.
--
--   Submodularity gives only "$\le$" in the displayed relation; the claim says that when equality holds, spanning passes to the intersection. In the proof of Claim 2.4 it shows that the intersection of two tight sets still dominates a vertex.
--
--   **Formalization Note** $r_M$ is `Matroid.eRk` ($\mathbb{N}_\infty$-valued, finite since $S$ is finite) and $\mathrm{Span}_M(Q)=\{s: r_M(Q\cup\{s\})=r_M(Q)\}$ as in the paper.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4, Claim 2.1

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph

namespace BasicPackArb.Main

/-- Claim 2.1 (p. 4). Let `M` be a matroid on `S` and `P, Q ⊆ S` with
`r_M(P ∩ Q) + r_M(P ∪ Q) = r_M(P) + r_M(Q)`, and `s ∈ Span_M(P) ∩ Span_M(Q)`.
Then `s ∈ Span_M(P ∩ Q)`. -/
theorem claim_2_1 {S : Type*} [Fintype S] (M : Matroid S) (hM : M.E = Set.univ)
    (P Q : Set S) (s : S)
    (hmod : M.eRk (P ∩ Q) + M.eRk (P ∪ Q) = M.eRk P + M.eRk Q)
    (hs : s ∈ Span M P ∩ Span M Q) :
    s ∈ Span M (P ∩ Q) := by sorry

end BasicPackArb.Main
