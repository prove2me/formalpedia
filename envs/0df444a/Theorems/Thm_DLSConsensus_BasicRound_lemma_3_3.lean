-- Prove2me | Theorems.Thm_DLSConsensus_BasicRound_lemma_3_3
-- name    : DLSConsensus.BasicRound.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:43:52.624365+00:00
-- url     : https://prove2.me/theorems/50d3b51f-870a-4e80-b2d1-deda22e1a2ac
-- title:
--   Lemma 3.3 — after a lock-release phase at or after GST, correct processors lock at most one value
-- statement:
--   Consider any run of Algorithm 1 in the basic round model whose delivery pattern is allowed for the set $C$ of correct processors and the round $\mathrm{GST}$ (every message between processors of $C$ sent at a round $\ge \mathrm{GST}$ is delivered). Let $k\ge1$ with $\mathrm{GST}\le 4k$, so that lock-release phase $k$ (round $4k$) occurs at or after GST. Then, immediately after round $4k$, the set
--   $$\{\, v\in V : \text{some } p\in C \text{ has a lock on } v \,\}$$
--   contains at most one value.
--
--   This is the step of the termination proof that guarantees that, after GST, the owner of the next trying phase finds a value acceptable to all correct processors.
--
--   **Formalization Note** "Immediately after" is the state after the computation subround of round $4k$. A processor's lock-release message to itself is subject to the same delivery rule as any other message, so it is delivered when the processor is in $C$ and the round is at or after GST.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 297, Lemma 3.3

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.3 (p. 297): immediately after any lock-release phase `k` (round `4k`) that occurs at
or after GST, the set of values locked by processors in `C` has at most one element. -/
theorem lemma_3_3 {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (C : Finset (Fin N)) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (k : ℕ) (hk : 1 ≤ k) (hGST : GST ≤ 4 * k) :
    {v : V | ∃ p ∈ C, (exec t pick init deliv (4 * k) p).lock v ≠ none}.Subsingleton := by sorry

end DLSConsensus.BasicRound
