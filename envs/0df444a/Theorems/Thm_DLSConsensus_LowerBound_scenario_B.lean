-- Prove2me | Theorems.Thm_DLSConsensus_LowerBound_scenario_B
-- name    : DLSConsensus.LowerBound.scenario_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:47:06.923167+00:00
-- url     : https://prove2.me/theorems/dac9e593-8563-40cf-a699-6d6010116fdb
-- title:
--   Proof of Theorem 4.3, Scenario B — with P initially dead and all inputs 1, the processors of Q decide 1 within some time T_B
-- statement:
--   Let $t \le N$ and let $\pi$ be a $t$-resilient consensus protocol achieving weak unanimity for binary values, with fail-stop faults, synchronous processors ($\Phi = 1$), and communication in which either $\Delta$ holds eventually (for a positive integer $\Delta$) or delta is unknown. Divide the $N$ processors into two disjoint groups $P$ and $Q$ with $P \cup Q$ all processors and
--   $$1 \le |P| \le t, \qquad 1 \le |Q| \le t.$$
--   **Scenario B**: all initial values are $1$, the processors of $P$ are initially dead, the processors of $Q$ take a step at every tick, and every message sent from a processor of $Q$ to a processor of $Q$ is delivered in time $1$. Then
--
--   1. a run of Scenario B exists, and
--   2. in every run of Scenario B there is a finite time $T_B$ such that every processor of $Q$ has decided by tick $T_B$, and its decision is $1$.
--
--   This is the mirror image of Scenario A, with the roles of $P$ and $Q$ and of the values $0$ and $1$ exchanged.
--
--   **Formalization Note** "Delivered in exactly time 1" is read as in Scenario A: no later than the addressee's first Receive at least one tick after the send. "Within $T_B$ steps for some finite $T_B$" is the explicit $\exists T_B$.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 306, proof of Theorem 4.3, Scenario B

import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario B of the proof of Theorem 4.3 (p. 306), symmetric to Scenario A. Let `π` be a
`t`-resilient consensus protocol achieving weak unanimity in the communication model `cm`, and split
the processors into two disjoint groups `P`, `Q` with `1 ≤ |P|, |Q| ≤ t`. Scenario B — all initial
values `1` (`true`), the processors of `P` initially dead, messages from `Q` to `Q` delivered in
time 1 — has a run, and in every such run there is a finite `T_B` by which every processor of `Q` has
decided, and decided `1`. -/
theorem scenario_B {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π Q true R) ∧
    ∀ R : Run N σ, IsolatedScenario π Q true R →
      ∃ TB : ℕ, ∀ i ∈ Q, ∃ n ≤ TB, DecidesAt π R i true n := by sorry

end DLSConsensus.LowerBound
