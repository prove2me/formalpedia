-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_24
-- name    : EarlyStoppingEIG.Exact.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:59.448608+00:00
-- url     : https://prove2.me/theorems/6825c4cc-82b7-41ff-90a1-1738a5d99581
-- title:
--   Lemma 24 — Agreement with sender outside the cover (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   Here $3\le r<t+1$ is the first honest termination round, $p$ is honest and halts in $r$, and $S$ is a cover accepted at $p$, with $p\notin S$ and $|S|\le r-2$, as in the preamble on page 27. The earliest-termination context implies all honest parties send through round $r$; this is not assumed as a proof lemma.
--
--   If $s\notin S$, party $p$ has received a valid signed sender bit $b$ in round one and every honest party outputs it:
--   $$m_{s\to p}^{(1)}=\langle b\rangle_s,\qquad \forall i\text{ honest},\quad y_i=b.$$
--   The sender receipt and bit are existential conclusions rather than additional assumptions.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 24, printed/PDF p.30; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 24, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.30.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_24 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (p : Party P) (r : ℕ) (S : Finset (Party P))
    (context : FirstCover P E p r S) (senderOut : P.sender ∉ S) :
    ∃ b v, ReceiptAt P E p 1 P.sender = some v ∧ IsSenderBit P v b ∧
      ∀ i, Honest P E i → Outputs P E i b := by sorry

end EarlyStoppingEIG.Exact
