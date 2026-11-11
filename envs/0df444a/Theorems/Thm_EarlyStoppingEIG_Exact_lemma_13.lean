-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_13
-- name    : EarlyStoppingEIG.Exact.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:44.289233+00:00
-- url     : https://prove2.me/theorems/19fc7493-3356-4fcb-8095-9475c3e6ea5c
-- title:
--   Lemma 13 — Equal final-round entries (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   If no honest party halts before round $t+1$, then for every all-faulty EIG path $w$ and every created entry $2\le u\le |w|$, honest parties’ final-round reconstructed entries coincide:
--   $$\operatorname{val}^{(u)}(\widehat w,i)=\operatorname{val}^{(u)}(\widehat w,k).$$
--   The horizon is exactly $t+1$; raw receipt trees need not be identical.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
--   - encoding: ΠOutput may return zero before the entry loop when no sender signature on one was observed → EntryAt denotes the mathematical reconstruction for the actual invocation’s snapshot even if that reconstruction need not be evaluated by the zero-return branch; reason: the entry equations denote the same local reconstruction; output retains the source’s immediate-zero test and no additional communication occurs
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 13, printed/PDF p.26; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 13, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.26.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_13 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (noneEarly : NoEarlierHonestHalt P E (P.t + 1))
    (i k : Party P) (hi : Honest P E i) (hk : Honest P E k)
    (w : List (Party P)) (path : IsPath P w) (faults : AllFaulty P E w)
    (u : ℕ) (lower : 2 ≤ u) (upper : u ≤ w.length) :
    EntryAt P E i (P.t + 1) w u = EntryAt P E k (P.t + 1) w u := by sorry

end EarlyStoppingEIG.Exact
