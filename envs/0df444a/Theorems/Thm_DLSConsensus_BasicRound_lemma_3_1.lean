-- Prove2me | Theorems.Thm_DLSConsensus_BasicRound_lemma_3_1
-- name    : DLSConsensus.BasicRound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:43:24.816021+00:00
-- url     : https://prove2.me/theorems/534d4fe1-e744-4bd3-8f6b-b8f128b9314f
-- title:
--   Lemma 3.1 — no two distinct values acquire locks with the same associated phase
-- statement:
--   Consider any run of Algorithm 1 in the basic round model, with arbitrary initial values, delivery pattern and choice function. Say that a processor **locks $v$ at phase $k$** ($k\ge1$) if it receives the message $(\mathrm{lock}\ v,k)$ in round $4k-2$.
--
--   It is impossible for two distinct values to acquire locks with the same associated phase: for all processors $p,q$, all $k\ge1$ and all values $v,w$,
--   $$p \text{ locks } v \text{ at phase } k \ \text{ and } \ q \text{ locks } w \text{ at phase } k \ \Longrightarrow\ v=w.$$
--
--   Phase numbers thus identify the locked value uniquely; this is used in the proof of Lemma 3.2 to exclude a competing lock with the same phase.
--
--   **Formalization Note** No hypothesis on $t$, on the delivery pattern or on the choice function is needed, and none is assumed.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 296, Lemma 3.1

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.1 (p. 296): it is impossible for two distinct values to acquire locks with the same
associated phase. If processor `p` locks `v` at phase `k` and processor `q` locks `w` at the
same phase `k`, then `v = w`. -/
theorem lemma_3_1 {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (k : ℕ) (p q : Fin N) (v w : V)
    (hp : LocksAt t pick init deliv p k v) (hq : LocksAt t pick init deliv q k w) :
    v = w := by sorry

end DLSConsensus.BasicRound
