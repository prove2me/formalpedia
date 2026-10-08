-- Prove2me | Theorems.Thm_DLSConsensus_LowerBound_scenario_A
-- name    : DLSConsensus.LowerBound.scenario_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:47:02.296987+00:00
-- url     : https://prove2.me/theorems/bceda0fb-9451-4eff-ae66-9af59fbbf267
-- title:
--   Proof of Theorem 4.3, Scenario A — with Q initially dead and all inputs 0, the processors of P decide 0 within some time T_A
-- statement:
--   Let $t \le N$ and let $\pi$ be a $t$-resilient consensus protocol achieving weak unanimity for binary values, with fail-stop faults, synchronous processors ($\Phi = 1$), and communication in which either $\Delta$ holds eventually (for a positive integer $\Delta$) or delta is unknown. Divide the $N$ processors into two disjoint groups $P$ and $Q$ with $P \cup Q$ all processors and
--   $$1 \le |P| \le t, \qquad 1 \le |Q| \le t.$$
--   **Scenario A**: all initial values are $0$, the processors of $Q$ are initially dead (they never take a step), the processors of $P$ take a step at every tick, and every message sent from a processor of $P$ to a processor of $P$ is delivered in time $1$. Then
--
--   1. a run of Scenario A exists, and
--   2. in every run of Scenario A there is a time $T_A$ such that every processor of $P$ has decided by tick $T_A$, and its decision is $0$.
--
--   This is the first of the three scenarios in the proof of Theorem 4.3: it fixes what the group $P$ does on its own when every input is $0$.
--
--   **Formalization Note** "Delivered in exactly time 1" is read as: delivered no later than the addressee's first Receive at a tick at least one after the send. A step is either a Send or a Receive, so a processor that sends at the next tick cannot receive then; delivery at that first Receive is the earliest delivery the model allows. "Reach a decision within time $T_A$" is the explicit $\exists T_A$; "decides 0 by $T_A$" means its first decision, at a tick $n \le T_A$, is $0$.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), pp. 305–306, proof of Theorem 4.3, Scenario A

import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario A of the proof of Theorem 4.3 (p. 305). Let `π` be a `t`-resilient consensus protocol
achieving weak unanimity in the communication model `cm` (Δ holds eventually, with `Δ > 0`, or delta
is unknown), and split the processors into two disjoint groups `P`, `Q` with `1 ≤ |P|, |Q| ≤ t`.
Scenario A — all initial values `0` (`false`), the processors of `Q` initially dead, messages from `P`
to `P` delivered in time 1 — has a run, and in every such run there is a time `T_A` by which every
processor of `P` has decided, and decided `0`. -/
theorem scenario_A {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π P false R) ∧
    ∀ R : Run N σ, IsolatedScenario π P false R →
      ∃ TA : ℕ, ∀ i ∈ P, ∃ n ≤ TA, DecidesAt π R i false n := by sorry

end DLSConsensus.LowerBound
