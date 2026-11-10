-- Prove2me | Theorems.Thm_CharonChurn_Main_theorem_22
-- name    : CharonChurn.Main.theorem_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:57:55.420555+00:00
-- url     : https://prove2.me/theorems/c8ec0b0b-0df5-4df4-bd60-dd8873fba1bc
-- title:
--   Theorem 22 — correctness and classification guarantees
-- statement:
--   Throughout, $i$ is an eligible correct verifier for the window $[s,e]$, $e=s+\tau-1$ (correct, present throughout $[s,e+L_{\mathrm{flood}}]$, window inside the session current at round $e+L_{\mathrm{flood}}$), with complete target-window evidence at its assessment round $e+L_{\mathrm{flood}}$, in an execution satisfying all standing assumptions; all objects are computed from $i$'s retained evidence at that round. Then: (i) if $\kappa(G^*)\le t$ it outputs Partitionable; (ii) if it outputs Not Partitionable then $\kappa(G^*)>t$; (iii) if $\kappa(G^*)>3t-\mu$ it outputs Not Partitionable; (iv) if it makes a structural Partitionable decision after the eligibility, coverage and budget guards pass, then $\kappa(G^*)\le3t-\mu$. Consequently $\kappa(G^*)>3t$ is a uniform sufficient condition for Not Partitionable.
--
--   Differences from the source:
--   - reading: Charon does not claim exact classification for every graph in the intermediate range t < κ(G*) ≤ 3t → not formalized; reason: a disclaimer of what is not asserted; it has no mathematical content to state
--   - reading: eligible correct verifier (assessing the window [s,e]) → i ∉ B, i present in every round of [s, e + L_flood] with e = s + τ − 1, and session(s) = session(e + L_flood); reason: §2.7 eligibility: present throughout [s_r, r] and the target window inside the session current at the assessment round r = e + L_flood
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Theorem 22, p. 31 (PDF 31)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Theorem 22 (Correctness and classification guarantees), p. 31. At every eligible correct
verifier assessing a target window with complete evidence: (i) `κ(G*) ≤ t` ⇒ Partitionable;
(ii) Not Partitionable ⇒ `κ(G*) > t`; (iii) `κ(G*) > 3t − μ` ⇒ Not Partitionable; (iv) a
structural Partitionable decision taken after the eligibility, coverage and budget guards pass
implies `κ(G*) ≤ 3t − μ`; consequently `κ(G*) > 3t` ⇒ Not Partitionable. -/
theorem theorem_22 (E : Execution) (hE : E.Legal) (s i : ℕ)
    (helig : E.EligibleVerifier s i)
    (hcomplete : E.CompleteEvidence (E.assessAt s) i s (E.wEnd s)) :
    let I := E.assessInput s i
    let κs := kappaStar E.N s (E.wEnd s)
    (κs ≤ E.P.t → E.decision (E.assessAt s) i = Verdict.partitionable) ∧
    (E.decision (E.assessAt s) i = Verdict.notPartitionable → E.P.t < κs) ∧
    (3 * (E.P.t : ℤ) - (E.muAt (E.assessAt s) i : ℤ) < (κs : ℤ) →
      E.decision (E.assessAt s) i = Verdict.notPartitionable) ∧
    (I.GuardsPass → E.decision (E.assessAt s) i = Verdict.partitionable →
      (κs : ℤ) ≤ 3 * (E.P.t : ℤ) - (E.muAt (E.assessAt s) i : ℤ)) ∧
    (3 * E.P.t < κs → E.decision (E.assessAt s) i = Verdict.notPartitionable) := by sorry

end CharonChurn.Main
