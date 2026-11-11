-- Prove2me | Theorems.Thm_EarlyStoppingEIG_Exact_lemma_9
-- name    : EarlyStoppingEIG.Exact.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:00:00.10162+00:00
-- url     : https://prove2.me/theorems/748e95fd-26f3-4142-98ea-467439e8b4a1
-- title:
--   Lemma 9 — All three honest-party entry clauses (corrected: round-one halt when t=0)
-- statement:
--   Let $n,t\in\mathbb N$ satisfy $2t<n$, let $s$ be any designated sender, let its private input be binary, and consider any legal synchronous execution with authenticated channels, plain PKI and ideal signatures. Corruptions are strongly adaptive, may delete pending messages of newly corrupted parties, and obey the threshold $t$. A party is honest if it is never corrupted.
--
--   Let honest $i$ invoke the output subroutine at its actual horizon $h$, and let $w$ be a path of depth $2\le d\le h$ ending at honest $j$. All three entry clauses hold:
--   1. For $2\le u\le d$, any signed message $m_j^{(u)}$ sent by $j$ gives $\operatorname{val}^{(u)}(\widehat w,i)=\{m_j^{(u)}\}$.
--   2. Round-two halting by $j$ with bit $b$ gives $\operatorname{val}^{(3)}(\widehat w,i)=\{V_b\}$ on the created-entry domain $3\le d$.
--   3. Halting before round $4\le u\le d$ gives $\operatorname{val}^{(u)}(\widehat w,i)=\star$.
--
--   $$2\le u\le d\le h.$$
--   Internal nodes as well as leaves are included; the reconstructed set can have other shapes when the ending party is faulty.
--
--   Differences from the source:
--   - correction: the printed protocol has no round-one output or halt branch when t=0 → ΠBB outputs the sender bit and halts at the end of round one when t=0, and retains the printed rules for t>0; reason: n=2,t=f=0,input 1,all honest satisfies every source assumption but the printed rounds 2 through t+1 are empty, so nobody halts; the added branch is the minimal documented correction
--   - encoding: named parties, binary inputs, ideal signatures, local receipts and synchronous adaptive executions → Fin n, Bool, symbolic signed finite terms, optional exact receipts, and finite ordered action traces per round; reason: these represent the same source objects; corruption reveals only current keys and memory, deletion acts on pending packets, and local transitions have no access to F, f or another party’s private input
--   - reading: one valid direct receipt per party and round, with malformed reports ignored → ignore ill-formed signed reports and retain the first valid channel message in delivery order; reason: the source stores a single exact receipt; arbitrary delivery order permits any valid choice by a Byzantine sender without restricting its wire behavior
--   - reading: the round-three entry clause is printed without a separate depth guard → the clause is asserted on the created-entry domain, so depth is at least three; reason: ΠOutput creates only entries with 2≤u≤depth≤h; this avoids referring to a nonexistent round-three entry at depth two
--   - generalization: a computationally bounded Byzantine adversary using ideal signatures → any finite sequence of derivable Byzantine actions per round under the same ideal authentication rule, without a computation bound; reason: every source execution is admitted, and no quantitative computation or communication claim is made; the assertions concern only the resulting authenticated traces
--   - encoding: ΠOutput may return zero before the entry loop when no sender signature on one was observed → EntryAt denotes the mathematical reconstruction for the actual invocation’s snapshot even if that reconstruction need not be evaluated by the zero-return branch; reason: the entry equations denote the same local reconstruction; output retains the source’s immediate-zero test and no additional communication occurs
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), Lemma 9, printed/PDF p.24; §§2–4, pp.15–31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_StatementContext

namespace EarlyStoppingEIG.Exact

/-- Lemma 9, Deligios et al., STOC 2027 submission #196
(October 2026), printed/PDF p.24.
This statement concerns the concrete operational execution and local subroutines
of Sections 2–4, not a correctness certificate supplied as a hypothesis. -/
theorem lemma_9 (P : Parameters) (input : Bool) (E : Execution P)
    (run : IsExecution P input E)
    (i j : Party P) (h : ℕ) (w : List (Party P))
    (hi : Honest P E i) (hj : Honest P E j) (snapshot : OutputSnapshot P E i h)
    (path : IsPath P w) (depth : 2 ≤ w.length) (horizon : w.length ≤ h)
    (last : w.getLast? = some j) :
    (∀ u m, 2 ≤ u → u ≤ w.length → SentAt P E j u m →
      EntryAt P E i h w u = {EntryAtom.signed m}) ∧
    (∀ b, 3 ≤ w.length → HaltsAt P E j 2 b →
      EntryAt P E i h w 3 = {EntryAtom.bitMarker b}) ∧
    (∀ u q b, 4 ≤ u → u ≤ w.length → q < u → HaltsAt P E j q b →
      EntryAt P E i h w u = {EntryAtom.star}) := by sorry

end EarlyStoppingEIG.Exact
