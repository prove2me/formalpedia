-- Prove2me | Theorems.Thm_CharonChurn_Main_theorem_24
-- name    : CharonChurn.Main.theorem_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:57:54.57836+00:00
-- url     : https://prove2.me/theorems/eedb04ca-1f33-4022-8f0a-a92290180355
-- title:
--   Theorem 24 — evidence-stabilization bound
-- statement:
--   Let $\Gamma=\tau+L_{\mathrm{flood}}$. Suppose the parameter assumptions, $|B|\le t$, the identity/session model, the signing interface, correct-envelope format compatibility (ReportsFit), and the no-forgery conditional hold, the physical-graph, spectral-gap and churn hypotheses hold in every round of $[r_0+1,r_0+\Gamma]$ (and every transition inside it), the target window $[r_0+1,r_0+\tau]$ lies in the session current at round $r_0+\Gamma$, and a correct node $i$ is present throughout $[r_0+1,r_0+\Gamma]$. Then the window assessed at round $r_0+\Gamma$ is exactly $[r_0+1,r_0+\tau]$, by the beginning of round $r_0+\Gamma$ node $i$ has complete evidence for it and is eligible to assess it, and the guarantees of Theorem 22 (i)–(iv) and the uniform $3t$ condition hold for this window according to its persistent-graph connectivity.
--
--   Differences from the source:
--   - reading: the physical-graph, spectral-gap and churn hypotheses of Theorem 12 hold in every round needed to disseminate reports from the target window → round assumptions for every r ∈ [r₀+1, r₀+Γ] and the churn bound for every transition r → r+1 with r ∈ [r₀+1, r₀+Γ−1]; parameter assumptions, |B| ≤ t and the identity/session model globally; reason: reports of rounds r₀+1..r₀+τ are disseminated during [r₀+1, r₀+τ+L_flood]
--   - reading: the target window lies wholly within the current session → session(r₀+1) = session(r₀+Γ); reason: current = the session active at the assessment round, as eligibility requires (§2.7); with sessions contiguous this puts the whole window and assessment in one session
--   - reading: they apply to each subsequent assessed window only when that window satisfies the corresponding connectivity condition and i remains eligible → no separate clause: the theorem is quantified over every r₀; reason: the sentence restricts, rather than adds to, the guarantee
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Theorem 24, p. 32 (PDF 32)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Theorem 24 (Evidence-stabilization bound), p. 32. Let `Γ = τ + L_flood`. Suppose the
physical-graph, spectral-gap and churn hypotheses hold in every round of `[r₀ + 1, r₀ + Γ]` (the
rounds needed to disseminate the target window's reports), the target window
`[r₀ + 1, r₀ + τ]` lies in the session current at the assessment round, and correct `i` is
present throughout `[r₀ + 1, r₀ + Γ]`. Then at round `r₀ + Γ` node `i` has complete evidence for
the window and is eligible to assess it, and the guarantees of Theorem 22 hold for this window. -/
theorem theorem_24 (E : Execution) (hP : ParamsOK E.P) (hB : E.N.B.card ≤ E.P.t)
    (hId : IdModel E.N) (hsign : ∀ u p, E.Cr.verify u p (E.Cr.sign u p) = true)
    (hnf : E.NoForgery) (hfit : E.ReportsFit) (r₀ : ℕ)
    (hround : ∀ r ∈ Finset.Icc (r₀ + 1) (r₀ + Gamma E.P), RoundOK E.P E.N r)
    (hchurn : ∀ r ∈ Finset.Ico (r₀ + 1) (r₀ + Gamma E.P), ChurnOK E.P E.N r)
    (hsession : E.N.session (r₀ + 1) = E.N.session (r₀ + Gamma E.P))
    (i : ℕ) (hi : i ∉ E.N.B)
    (hpresent : ∀ m ∈ Finset.Icc (r₀ + 1) (r₀ + Gamma E.P), i ∈ E.N.V m) :
    let r := r₀ + Gamma E.P
    let I := E.inputAt r i
    let κs := kappaStar E.N (r₀ + 1) (r₀ + E.P.τ)
    E.winStart r = r₀ + 1 ∧ E.winEnd r = r₀ + E.P.τ ∧
    E.CompleteEvidence r i (r₀ + 1) (r₀ + E.P.τ) ∧ E.Eligible r i ∧
    (κs ≤ E.P.t → E.decision r i = Verdict.partitionable) ∧
    (E.decision r i = Verdict.notPartitionable → E.P.t < κs) ∧
    (3 * (E.P.t : ℤ) - (E.muAt r i : ℤ) < (κs : ℤ) →
      E.decision r i = Verdict.notPartitionable) ∧
    (I.GuardsPass → E.decision r i = Verdict.partitionable →
      (κs : ℤ) ≤ 3 * (E.P.t : ℤ) - (E.muAt r i : ℤ)) ∧
    (3 * E.P.t < κs → E.decision r i = Verdict.notPartitionable) := by sorry

end CharonChurn.Main
