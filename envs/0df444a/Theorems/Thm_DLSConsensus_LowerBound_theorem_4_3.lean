-- Prove2me | Theorems.Thm_DLSConsensus_LowerBound_theorem_4_3
-- name    : DLSConsensus.LowerBound.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:47:16.122731+00:00
-- url     : https://prove2.me/theorems/0da974da-94d8-4e7a-b934-5226e3fb3586
-- title:
--   Theorem 4.3 — with synchronous processors and partially synchronous communication, no t-resilient consensus for 2 ≤ N ≤ 2t fail-stop
-- statement:
--   Consider $N$ processors with binary initial values, fail-stop faults, synchronous processors ($\Phi = 1$: every correct processor takes a step at every tick of real time), and partially synchronous communication, in either of its two forms: $\Delta$ holds eventually (for a fixed positive integer $\Delta$ known to the protocol designer, holding from some unknown global stabilization time on), or delta is unknown (some positive $\Delta$ holds from the start, but the protocol is fixed before $\Delta$). Let $t$ be an integer with $0 \le t \le N$ and assume
--   $$2 \le N \le 2t.$$
--   Then there is no $t$-resilient consensus protocol that achieves weak unanimity for binary values. Explicitly:
--
--   1. for every positive integer $\Delta$, no protocol is a $t$-resilient consensus protocol achieving weak unanimity when $\Delta$ holds eventually;
--   2. no protocol is a $t$-resilient consensus protocol achieving weak unanimity when delta is unknown.
--
--   The state set and message set of the protocol are arbitrary and may be infinite.
--
--   The theorem shows that the resiliency $N \ge 2t + 1$ of the paper's protocols for fail-stop and omission faults (Theorems 4.1 and 4.2, part (a)) cannot be improved, even for weak unanimity and a binary value domain.
--
--   **Formalization Note** The paper states the theorem for "fail-stop or omission faults"; its proof assumes an algorithm immune to fail-stop faults. The Lean states the fail-stop impossibility, which implies the omission case: a fail-stop processor behaves, as seen by the others, like a processor whose sends are all omitted from its stop time on, so every protocol that is $t$-resilient against omission faults is $t$-resilient against fail-stop faults. The omission case is not a separate item. In part 1, $\Delta$ is chosen before the protocol, as in the paper's game reading ("the adversary picks $\Delta$, the designer (knowing $\Delta$) supplies a consensus protocol"); in part 2 the protocol is fixed first and the allowed runs carry their own $\Delta$. The bound $t \le N$ is the range of $t$ in the paper's definition of $t$-resilience (§2.4).
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 305, Theorem 4.3

import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Theorem 4.3 (Dwork, Lynch, Stockmeyer 1988, p. 305), fail-stop case: with synchronous processors
(Φ = 1) and partially synchronous communication — (a) Δ holds eventually, for every positive Δ, or
(b) delta is unknown — and `2 ≤ N ≤ 2t` (with the standing `t ≤ N` of §2.4), no protocol for binary
values is a `t`-resilient consensus protocol achieving weak unanimity. The state and message types
of the protocol are arbitrary (possibly infinite). -/
theorem theorem_4_3 (N t : ℕ) (hN : 2 ≤ N) (hNt : N ≤ 2 * t) (htN : t ≤ N) :
    (∀ Δ : ℕ, 0 < Δ → ∀ (σ M : Type) (π : Protocol N σ M),
      ¬ Resilient π t (Comm.eventually Δ)) ∧
    (∀ (σ M : Type) (π : Protocol N σ M), ¬ Resilient π t Comm.unknown) := by sorry

end DLSConsensus.LowerBound
