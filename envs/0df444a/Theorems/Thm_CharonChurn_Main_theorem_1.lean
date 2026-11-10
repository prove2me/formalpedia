-- Prove2me | Theorems.Thm_CharonChurn_Main_theorem_1
-- name    : CharonChurn.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:58:00.686137+00:00
-- url     : https://prove2.me/theorems/86d366b7-a1cf-4d90-abd6-1b92aa8d7d42
-- title:
--   Theorem 1 — main guarantees of Charon
-- statement:
--   Three parts.
--
--   (a) The dissemination horizon $L_{\mathrm{flood}}=2\lceil4/\hat\lambda_0\rceil+\lceil6\ln n/\hat\lambda_0\rceil+\lceil4\ln n/\hat\lambda_0\rceil+4$ is $O((\log n+1)/\hat\lambda_0)$: there is one absolute constant $C$ with $L_{\mathrm{flood}}(n,\hat\lambda_0)\le C(\ln n+1)/\hat\lambda_0$ for all $n$ and all $\hat\lambda_0\in(0,1]$.
--
--   (b) Polynomial local computation: some Turing machine computes Charon's decision from the binary encoding of the public context and retained evidence in time polynomial in the encoding length.
--
--   (c) Consider any execution satisfying the network, Byzantine-fault, churn and authentication assumptions, from arbitrary initial and joining caches and with arbitrary Byzantine messages of arbitrary finite size. Let $[s,e]$, $e=s+\tau-1$, be a target window inside the session, $G^*$ its persistent graph, and $i$ a correct verifier present throughout $[s,e+L_{\mathrm{flood}}]$. At round $e+L_{\mathrm{flood}}$, after validating and retaining the evidence disseminated to it, $i$ has the complete evidence for the window and is eligible, and its recomputed decision satisfies: 1. if $\kappa(G^*)\le t$ it outputs Partitionable; 2. if it outputs Not Partitionable then $\kappa(G^*)>t$; 3. if $\kappa(G^*)>3t-\mu_i$ it outputs Not Partitionable, where $\mu_i$ is the size of its forced-suspect set after closure; in particular $\kappa(G^*)>3t$ suffices for Not Partitionable.
--
--   Differences from the source:
--   - encoding: L_flood = O((log n + 1)/λ̂₀), with L_flood the deterministic evidence-dissemination horizon → L_flood is the exact ceiling formula of Theorem 12, and ∃ C, ∀ n, ∀ λ ∈ (0,1], L_flood(n, λ) ≤ C (ln n + 1)/λ; reason: the source's horizon is that formula (§3.1, Theorem 12); the O-claim is an explicit uniform constant with the constant chosen before n and λ
--   - encoding: the decision procedure requires polynomial local computation in the size of the retained evidence → Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodeBool decisionBool): a TM computes the Boolean decision from the binary encoding of (n, D, t, session, s, e, eligibility bit, retained cache) within a polynomial of the encoding length; reason: Mathlib's polynomial-time notion on an explicit binary encoding; signature checks of incoming messages are validation, not the decision procedure, which reads already-retained evidence
--   - encoding: evidence dissemination takes L_flood rounds in a synchronous neighbor-to-neighbor model with arbitrary finite message sizes → messages are arbitrary finite record sets delivered in one round over current edges; the conclusion includes complete evidence at round e + L_flood; reason: this is the model of §2.1 and what 'takes L_flood rounds' delivers
--   - reading: a correct verifier i that remains present throughout [s, e + L_flood], after validating the complete evidence for the window and recomputing its decision → hypotheses: i ∉ B, present throughout [s, e + L_flood], session(s) = session(e + L_flood); conclusions: complete evidence and eligibility at round e + L_flood, and the three guarantees for the decision recomputed there; reason: §2.7 requires the target window to lie in the current session; completeness is derived from the protocol, not assumed
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
--   - generalization: the horizon bound and decision computation on admissible executions and retained evidence → the numerical bound for every natural n (including 0 and 1), and polynomial decision computation for every encoded DecisionInput; reason: admissible executions supply a positive n and a retained-evidence input; the extra numerical cases obey the same ceiling estimate (C = 16), and the same finite decision rules extend to arbitrary encoded inputs
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Theorem 1, p. 3 (PDF 3); §§2–3, pp. 7–18; Theorem 12, p. 22

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution
import Definitions.Def_CharonChurn_Main_Encoding

namespace CharonChurn.Main

/-- Theorem 1 (Main guarantees of Charon), p. 3.
* The dissemination horizon `L_flood = 2⌈4/λ̂₀⌉ + ⌈6 ln n/λ̂₀⌉ + ⌈4 ln n/λ̂₀⌉ + 4` is
  `O((log n + 1)/λ̂₀)`, with one absolute constant.
* The decision procedure is computable by a Turing machine in time polynomial in the length of
  the binary encoding of the public context and the retained evidence.
* In every execution satisfying the network, Byzantine-fault, churn and authentication
  assumptions, from arbitrary initial and joining caches and arbitrary Byzantine messages: every
  correct verifier `i` present throughout `[s, e + L_flood]` (target window `[s, e]`,
  `e = s + τ − 1`, inside the session) has, at its assessment round `e + L_flood`, the complete
  evidence for the window, is eligible, and its recomputed decision satisfies:
  `κ(G*) ≤ t ⇒ Partitionable`; `Not Partitionable ⇒ κ(G*) > t`;
  `κ(G*) > 3t − μ_i ⇒ Not Partitionable`; and `κ(G*) > 3t ⇒ Not Partitionable`. -/
theorem theorem_1 :
    (∃ C : ℝ, ∀ (n : ℕ) (lam : ℝ), 0 < lam → lam ≤ 1 →
      (Lflood n lam : ℝ) ≤ C * ((Real.log n + 1) / lam)) ∧
    Nonempty (Turing.TM2ComputableInPolyTime encodeInput Computability.encodeBool decisionBool) ∧
    ∀ E : Execution, E.Legal → ∀ s i : ℕ, E.EligibleVerifier s i →
      let r := E.assessAt s
      let κs := kappaStar E.N s (E.wEnd s)
      E.CompleteEvidence r i s (E.wEnd s) ∧ (E.inputAt r i).eligible = true ∧
      (κs ≤ E.P.t → E.decision r i = Verdict.partitionable) ∧
      (E.decision r i = Verdict.notPartitionable → E.P.t < κs) ∧
      (3 * (E.P.t : ℤ) - (E.muAt r i : ℤ) < (κs : ℤ) →
        E.decision r i = Verdict.notPartitionable) ∧
      (3 * E.P.t < κs → E.decision r i = Verdict.notPartitionable) := by sorry

end CharonChurn.Main
