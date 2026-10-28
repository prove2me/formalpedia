-- Prove2me | Theorems.Thm_CommitOpen_Benign_cq_trace_distance
-- name    : CommitOpen.Benign.cq_trace_distance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:40.741765+00:00
-- url     : https://prove2.me/theorems/45f9ce7f-ed2c-4f45-959a-13dec3cc6a2d
-- title:
--   Proof of Lemma 4.3, p. 11 — the trace distance of two cq states over Test is the P_Test-average of the branch distances
-- statement:
--   Let $(\psi_{test})_{test}$ and $(\psi'_{test})_{test}$ be two families of vectors indexed by the tests $test=(T,T')$, $|T|=k$, $T'\subseteq T$, and let
--   $$\rho=\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\psi_{test}\rangle\langle\psi_{test}|,\qquad \rho'=\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\psi'_{test}\rangle\langle\psi'_{test}|.$$
--   Then
--   $$\delta(\rho,\rho')=\sum_{test}P_{Test}(test)\,\delta\big(|\psi_{test}\rangle\langle\psi_{test}|,\,|\psi'_{test}\rangle\langle\psi'_{test}|\big).$$
--
--   This is the first equality in the display on p. 11, with both sides un-squared (they are nonnegative). It reduces the distance between the real and the ideal cq states to a per-test computation.
--
--   **Formalization Note.** The cq states are block-diagonal matrices indexed by (test, basis vector); the identity is a theorem about their trace norm, not a definition.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 11, proof of Lemma 4.3 (second display, first equality)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem cq_trace_distance {m k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ ψ' : Test m k → EuclideanSpace ℂ ι) :
    traceDistance (cqState ψ) (cqState ψ') =
      ∑ t, testProb m k t * traceDistance (pureState (ψ t)) (pureState (ψ' t)) := by sorry

end CommitOpen.Benign
