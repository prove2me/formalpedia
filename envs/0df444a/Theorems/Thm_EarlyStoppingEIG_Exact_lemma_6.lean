-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_6
-- name    : EarlyStoppingEIG.Exact.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:21.986283+00:00
-- url     : https://prove2.me/theorems/73167b07-b543-47cc-8070-718af0d4dd5e
-- title:
--   Lemma 6 — Exact early termination bound (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   Every honest party actually halts, with an output, by the exact deadline
--   $$\min\{f+2,t+1\}.$$
--   The actual fault count $f$ comes from the strongly adaptive trace, including deletions of pending messages after corruption. It is not an input to a party. The corrected zero-threshold branch retains $t=0$ and the one-round bound.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 6, printed/PDF p.23; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 6, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.23. Corrected round-one halt at t=0; see the protocol definition.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_6 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    : ∀ i, Honest P E i → HaltsBy P E i (min ((faulty P E).card + 2) (P.t + 1)) := by sorry

end EarlyStoppingEIG.Exact
