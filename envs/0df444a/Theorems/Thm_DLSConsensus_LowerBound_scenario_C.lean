-- Prove2me | Theorems.Thm_DLSConsensus_LowerBound_scenario_C
-- name    : DLSConsensus.LowerBound.scenario_C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:47:08.458888+00:00
-- url     : https://prove2.me/theorems/995c7f20-82f8-42ec-ab70-23382a4c370c
-- title:
--   Proof of Theorem 4.3, Scenario C — all processors alive, cross-group messages delayed past T: P acts as in Scenario A and Q as in Scenario B
-- statement:
--   Let $\pi$ be any protocol, and fix the communication model: either $\Delta$ holds eventually (for a positive integer $\Delta$) or delta is unknown. Let $P, Q$ be disjoint groups covering all $N$ processors, let $R_A$ be a run of Scenario A (all initial values $0$, $Q$ initially dead, $P$ stepping at every tick, $P \to P$ messages delivered in time $1$) and $R_B$ a run of Scenario B (all initial values $1$, $P$ initially dead, $Q$ stepping at every tick, $Q \to Q$ messages delivered in time $1$), and let $T$ be any time. **Scenario C**: there is a run $R$ allowed by the communication model such that
--
--   1. all processors are alive (every processor takes a step at every tick);
--   2. processors of $P$ have initial value $0$ and processors of $Q$ have initial value $1$;
--   3. messages from $P$ to $P$ and from $Q$ to $Q$ are delivered in time $1$;
--   4. no message from $P$ to $Q$ or from $Q$ to $P$ is delivered at a tick $\le T$;
--   5. for every tick $n \le T$, each processor of $P$ is in the same state after tick $n$ in $R$ as in $R_A$, and each processor of $Q$ is in the same state as in $R_B$:
--   $$\mathrm{state}^R_i(n) = \mathrm{state}^{R_A}_i(n)\ (i \in P), \qquad \mathrm{state}^R_i(n) = \mathrm{state}^{R_B}_i(n)\ (i \in Q), \qquad n \le T.$$
--
--   With $T = \max(T_A, T_B)$ this run contradicts consistency: the processors of $P$ decide $0$ and those of $Q$ decide $1$, while all processors are correct.
--
--   **Formalization Note** The paper says that cross-group messages "take more than $\max(T_A, T_B)$ steps to be delivered" and that the groups "act exactly as they do" in Scenarios A and B. The Lean states what the argument uses: no cross-group message is delivered at or before tick $T$, and the local states agree up to tick $T$. Taken literally, "every cross-group message takes more than $T$ steps" is not allowed when $\Delta$ holds eventually and $\Delta \le T$, because messages sent after the stabilization time must arrive within $\Delta$; delaying only the deliveries up to tick $T$ is allowed in both models. $T$ is arbitrary here; the proof takes $T = \max(T_A, T_B)$.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 306, proof of Theorem 4.3, Scenario C

import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario C of the proof of Theorem 4.3 (p. 306). Let `π` be any protocol, `cm` a communication
model (Δ holds eventually with `Δ > 0`, or delta is unknown), `P`, `Q` a partition of the processors,
`RA` a run of Scenario A (initial values `0`, `Q` initially dead, `P → P` in time 1), `RB` a run of
Scenario B (initial values `1`, `P` initially dead, `Q → Q` in time 1), and `T` any time (in the proof,
`T = max(T_A, T_B)`). Then there is a run allowed by `cm` in which all processors take a step at every
tick (all alive), processors of `P` start with `0` and those of `Q` with `1`, messages from `P` to `P`
and from `Q` to `Q` are delivered in time 1, no message between the groups is delivered at a tick
`≤ T`, and every processor of `P` (resp. `Q`) is in the same state after each tick `n ≤ T` as in `RA`
(resp. `RB`). -/
theorem scenario_C {N : ℕ} {σ M : Type} (π : Protocol N σ M) (cm : Comm) (hcm : cm.WF)
    (P Q : Finset (Fin N)) (hdisj : Disjoint P Q) (hcover : P ∪ Q = Finset.univ)
    (RA RB : Run N σ) (hA : IsolatedScenario π P false RA) (hB : IsolatedScenario π Q true RB)
    (T : ℕ) :
    ∃ R : Run N σ, IsRun π R ∧ cm.Allowed π R ∧ FailStop Finset.univ R ∧
      (∀ i ∈ P, R.val i = false) ∧ (∀ i ∈ Q, R.val i = true) ∧
      TimeOneWithin π P R ∧ TimeOneWithin π Q R ∧
      (∀ k i s n, (k, s) ∈ R.deliv i n → (k ∈ P ↔ i ∈ Q) → T < n) ∧
      (∀ i ∈ P, ∀ n ≤ T, R.state i n = RA.state i n) ∧
      (∀ i ∈ Q, ∀ n ≤ T, R.state i n = RB.state i n) := by sorry

end DLSConsensus.LowerBound
