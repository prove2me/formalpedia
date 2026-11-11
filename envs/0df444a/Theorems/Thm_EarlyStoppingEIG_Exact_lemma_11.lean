-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_11
-- name    : EarlyStoppingEIG.Exact.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:22.988755+00:00
-- url     : https://prove2.me/theorems/a929ebed-fe1d-4662-9308-bdb220c50e19
-- title:
--   Lemma 11 — Agreement after round-2 termination (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   If an honest party halts in round $2<t+1$ with output $b$, then every honest party eventually outputs the same bit:
--   $$\forall j\text{ honest},\quad y_j=b.$$
--   Other honest parties may halt later and use different reconstruction horizons.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 11, printed/PDF p.25; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 11, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.25.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_11 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (i : Party P) (b : Bool) (hi : Honest P E i)
    (early : 2 < P.t + 1) (stop : HaltsAt P E i 2 b) :
    ∀ j, Honest P E j → Outputs P E j b := by sorry

end EarlyStoppingEIG.Exact
