-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_4
-- name    : EarlyStoppingEIG.Exact.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:59:44.563642+00:00
-- url     : https://prove2.me/theorems/6b0ef86e-98c4-4fdc-a549-10b665beb50c
-- title:
--   Lemma 4 — Honest forwarding (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   Let $i,j$ be honest parties and $w$ an EIG path not containing $j$. If both parties are active in round $|w|+1$, then the raw child value in $i$’s tree equals the raw parent value in $j$’s tree:
--   $$\operatorname{val}(\widehat{wj},i)=\operatorname{val}(\widehat w,j).$$
--   This concerns raw forwarded receipts, not reconstructed message sets.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 4, printed/PDF p.22; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 4, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.22.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_4 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (i j : Party P) (w : List (Party P))
    (hi : Honest P E i) (hj : Honest P E j) (path : IsPath P w) (outside : j ∉ w)
    (ai : Active P E i (w.length + 1)) (aj : Active P E j (w.length + 1)) :
    rawValue P ((E.state (w.length + 1)).views i) (w ++ [j]) =
      rawValue P ((E.state w.length).views j) w := by sorry

end EarlyStoppingEIG.Exact
