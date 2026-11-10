-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_16
-- name    : CharonChurn.Main.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:57:55.408001+00:00
-- url     : https://prove2.me/theorems/8301e081-910d-48bb-8982-9ffc7b5d96e9
-- title:
--   Lemma 16 — conflict-cover budget
-- statement:
--   Throughout, $i$ is an eligible correct verifier for the window $[s,e]$, $e=s+\tau-1$ (correct, present throughout $[s,e+L_{\mathrm{flood}}]$, window inside the session current at round $e+L_{\mathrm{flood}}$), with complete target-window evidence at its assessment round $e+L_{\mathrm{flood}}$, in an execution satisfying all standing assumptions; all objects are computed from $i$'s retained evidence at that round. Let $M$ be any maximal matching of the residual conflict graph $C_0=C[\hat V\setminus S]$, $q=|M|$ and $F=S\cup V(M)$. Then $B\setminus S$ vertex-covers $C_0$; $|F|=\mu+2q$; $q\le t-\mu$; $|B\setminus F|\le t-\mu-q$; and the fail-closed guards of the execution are not triggered (the initial and closed suspect sets have at most $t$ elements and $\mu+q_i\le t$ for Charon's own matching).
--
--   Differences from the source:
--   - encoding: q ≤ t − μ and |B \ F| ≤ t − μ − q → the same inequalities in ℤ; reason: avoids truncated natural subtraction
--   - reading: the fail-closed budget conditions μ > t and μ + q > t cannot be triggered in such an execution → for Charon's actual computation: |S₀| ≤ t, μ ≤ t and μ + q_i ≤ t with q_i the size of Charon's greedy matching; reason: the guards checked by Algorithm 1 (lines 10, 14, 18) are those of the execution's own matching
--   - reading: eligible correct verifier (assessing the window [s,e]) → i ∉ B, i present in every round of [s, e + L_flood] with e = s + τ − 1, and session(s) = session(e + L_flood); reason: §2.7 eligibility: present throughout [s_r, r] and the target window inside the session current at the assessment round r = e + L_flood
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 16, p. 27 (PDF 27–28)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Lemma 16 (Conflict-cover budget), p. 27. At an eligible verifier with complete evidence,
`B \ S` vertex-covers the residual conflict graph `C₀`; for any maximal matching `M` of `C₀`
with `q = |M|` and `F = S ∪ V(M)`: `|F| = μ + 2q`, `q ≤ t − μ`, `|B \ F| ≤ t − μ − q`; and
the fail-closed budget guards (`μ > t`, `μ + q > t`) of the execution are not triggered. -/
theorem lemma_16 (E : Execution) (hE : E.Legal) (s i : ℕ)
    (helig : E.EligibleVerifier s i)
    (hcomplete : E.CompleteEvidence (E.assessAt s) i s (E.wEnd s))
    (M : Finset (ℕ × ℕ))
    (hM : IsMaximalMatching ((E.assessInput s i).conflictGraph (E.assessInput s i).S) M) :
    let I := E.assessInput s i
    (∀ u v, (I.conflictGraph I.S).Adj u v → u ∈ E.N.B \ I.S ∨ v ∈ E.N.B \ I.S) ∧
    (I.Fof M).card = I.mu + 2 * M.card ∧
    (M.card : ℤ) ≤ (E.P.t : ℤ) - I.mu ∧
    (((E.N.B \ I.Fof M).card : ℕ) : ℤ) ≤ (E.P.t : ℤ) - I.mu - M.card ∧
    I.S0.card ≤ E.P.t ∧ I.mu ≤ E.P.t ∧ I.mu + I.qM ≤ E.P.t := by sorry

end CharonChurn.Main
