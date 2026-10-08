-- Prove2me | Theorems.Thm_DLSConsensus_BasicRound_decision_round_bound
-- name    : DLSConsensus.BasicRound.decision_round_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:43:45.546985+00:00
-- url     : https://prove2.me/theorems/da2957a4-c7e2-497a-a802-059c0c96584d
-- title:
--   Section 3.2.1, p. 298 — all correct processors decide by round GST + 4(N + 1)
-- statement:
--   Assume the basic round model with omission (in particular fail-stop) faults and $N\ge 2t+1$. Let $C$ be any set of at least $N-t$ processors, $\mathrm{GST}$ any round, $\mathrm{deliv}$ any delivery pattern allowed for $C$ and $\mathrm{GST}$, $\mathrm{init}$ any initial values in an arbitrary domain $V$, and $\mathrm{pick}$ any admissible choice function. Then every processor $p\in C$ decides some value $v$ at some phase $k$ whose decision round satisfies
--   $$4k-1 \ \le\ \mathrm{GST}+4(N+1).$$
--
--   This is the quantitative form of termination for Algorithm 1: decisions come at most a constant number of phases (linear in $N$) after GST.
--
--   **Formalization Note** The paper's "make decisions by round GST + 4(N+1)" is read as: the decision event (the computation subround of round $4k-1$ of the deciding phase $k$) happens at a round at most $\mathrm{GST}+4(N+1)$.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 298, Section 3.2.1 (sentence after the proof of Theorem 3.1)

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Section 3.2.1, p. 298: under the hypotheses of Theorem 3.1, every processor in `C` decides at
some phase `k` whose decision round `4k - 1` is at most `GST + 4(N + 1)`. -/
theorem decision_round_bound {N t : ℕ} (hN : 2 * t + 1 ≤ N) {V : Type*} (init : Fin N → V)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (pick : ℕ → Set V → V) (hpick : PickAdmissible pick) :
    ∀ p ∈ C, ∃ (k : ℕ) (v : V),
      DecidesAt t pick init deliv p k v ∧ 4 * k - 1 ≤ GST + 4 * (N + 1) := by sorry

end DLSConsensus.BasicRound
