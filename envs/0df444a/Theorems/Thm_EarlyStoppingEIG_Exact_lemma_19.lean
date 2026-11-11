-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_19
-- name    : EarlyStoppingEIG.Exact.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:00:19.88307+00:00
-- url     : https://prove2.me/theorems/2f625766-5e3c-4c80-941d-e98384fb208e
-- title:
--   Lemma 19 — Retained messages equal direct receipts (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   Here $3\le r<t+1$ is the first honest termination round, $p$ is honest and halts in $r$, and $S$ is a cover accepted at $p$, with $p\notin S$ and $|S|\le r-2$, as in the preamble on page 27. The earliest-termination context implies all honest parties send through round $r$; this is not assumed as a proof lemma.
--
--   Let $w$ be all faulty with depth $d\le r-2$, ending at $j\notin S$. If honest $i$ invokes output at actual horizon $h\ge r-1$, and a signed round-$u$ message is retained for $2\le u\le d$, then it is exactly the direct receipt at $p$:
--   $$m_j^{(u)}\in\operatorname{val}^{(u)}(\widehat w,i)\implies m_{j\to p}^{(u)}=m_j^{(u)}.$$
--   The membership premise refers only to the signed-message summand, not a completion marker.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
--   - encoding: ΠOutput may return zero before the entry loop when no sender signature on one was observed → EntryAt denotes the mathematical reconstruction for the actual invocation’s snapshot even if that reconstruction need not be evaluated by the zero-return branch; reason: the entry equations denote the same local reconstruction; output retains the source’s immediate-zero test and no additional communication occurs
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 19, printed/PDF p.28; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 19, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.28.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_19 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (p : Party P) (r : ℕ) (S : Finset (Party P))
    (context : FirstCover P E p r S) (i j : Party P) (h u : ℕ)
    (hi : Honest P E i) (snapshot : OutputSnapshot P E i h) (horizon : r - 1 ≤ h)
    (w : List (Party P)) (path : IsPath P w) (faults : AllFaulty P E w)
    (depth : w.length ≤ r - 2) (last : w.getLast? = some j) (outside : j ∉ S)
    (lower : 2 ≤ u) (upper : u ≤ w.length) (m : Message P)
    (member : EntryAtom.signed m ∈ EntryAt P E i h w u) :
    ReceiptAt P E p u j = some m := by sorry

end EarlyStoppingEIG.Exact
