-- Prove2me | Theorems.Thm_DLSConsensus_BasicRound_theorem_3_1
-- name    : DLSConsensus.BasicRound.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:44:08.225459+00:00
-- url     : https://prove2.me/theorems/55cd61fe-3e22-44be-8aa8-04a5cc1a63d3
-- title:
--   Theorem 3.1 — for N ≥ 2t + 1, Algorithm 1 achieves consistency, strong unanimity and termination
-- statement:
--   Assume the basic round model with fail-stop or omission faults, and assume $N\ge 2t+1$. Then Algorithm 1 achieves consistency, strong unanimity and termination for an arbitrary value domain.
--
--   Precisely: for every value type $V$ and initial values $\mathrm{init}:\{p_1,\dots,p_N\}\to V$, every set $C$ of processors with $|C|\ge N-t$ (the correct processors), every round $\mathrm{GST}$, every delivery pattern in which all messages sent between processors of $C$ at rounds $\ge\mathrm{GST}$ are delivered (any other message may be lost), and every admissible choice of proposals, the run of Algorithm 1 satisfies
--
--   1. *consistency*: any two decisions by processors in $C$ are equal;
--   2. *strong unanimity*: if all $N$ initial values are $v$, every decision by a processor in $C$ is $v$;
--   3. *termination*: every processor in $C$ decides.
--
--   This is the upper-bound half of the paper's result for omission and fail-stop faults with partially synchronous communication: $N\ge 2t+1$ suffices, which the paper later shows to be optimal.
--
--   **Formalization Note** Faulty processors are processors outside $C$ that run Algorithm 1 but whose messages (sent and received) may be lost at any round; this omission model contains fail-stop. The arbitrary choice among candidates is a universally quantified admissible choice function. Runs of the basic model are infinite, so the paper's "if $R$ is infinite" in the termination condition is automatic.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 297, Theorem 3.1

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Theorem 3.1 (p. 297): in the basic round model with omission (in particular fail-stop)
faults, if `N ≥ 2t + 1`, Algorithm 1 achieves consistency, strong unanimity and termination
for an arbitrary value domain `V`: for every set `C` of at least `N - t` correct processors,
every round `GST`, every message-loss pattern allowed by the model, every initial values and
every admissible choice of proposals. -/
theorem theorem_3_1 {N t : ℕ} (hN : 2 * t + 1 ≤ N) {V : Type*} (init : Fin N → V)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (pick : ℕ → Set V → V) (hpick : PickAdmissible pick) :
    Consistency t pick init deliv C ∧ StrongUnanimity t pick init deliv C ∧
      Termination t pick init deliv C := by sorry

end DLSConsensus.BasicRound
