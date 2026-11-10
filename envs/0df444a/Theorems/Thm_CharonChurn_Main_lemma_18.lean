-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_18
-- name    : CharonChurn.Main.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:58:03.644261+00:00
-- url     : https://prove2.me/theorems/7429ecd0-b291-46bd-99c6-152b3b074782
-- title:
--   Lemma 18 — one-sided external-degree error
-- statement:
--   Throughout, $i$ is an eligible correct verifier for the window $[s,e]$, $e=s+\tau-1$ (correct, present throughout $[s,e+L_{\mathrm{flood}}]$, window inside the session current at round $e+L_{\mathrm{flood}}$), with complete target-window evidence at its assessment round $e+L_{\mathrm{flood}}$, in an execution satisfying all standing assumptions; all objects are computed from $i$'s retained evidence at that round. With $M,F,U,X,K$ as in Lemma 17 and $N_K(f)=|N_{G^*}(f)\cap K|$: for every $f\in F$, $N_K(f)\le d^{\mathrm{out}}_F(f)\le N_K(f)+|X|$, and therefore $N_K(f)\ge d^{\mathrm{out}}_F(f)-\alpha$ with $\alpha=t-\mu-q$.
--
--   Differences from the source:
--   - encoding: N_K(f) ≥ d_out_F(f) − α → the inequality in ℤ with α = t − μ − |M|; reason: avoids truncated subtraction
--   - reading: eligible correct verifier (assessing the window [s,e]) → i ∉ B, i present in every round of [s, e + L_flood] with e = s + τ − 1, and session(s) = session(e + L_flood); reason: §2.7 eligibility: present throughout [s_r, r] and the target window inside the session current at the assessment round r = e + L_flood
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 18, p. 29 (PDF 29)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Lemma 18 (One-sided external-degree error), p. 29. For every `f ∈ F`, with
`N_K(f) = |N_{G*}(f) ∩ K|`: `N_K(f) ≤ d_out_F(f) ≤ N_K(f) + |X|`, hence
`N_K(f) ≥ d_out_F(f) − α` with `α = t − μ − q`. -/
theorem lemma_18 (E : Execution) (hE : E.Legal) (s i : ℕ)
    (helig : E.EligibleVerifier s i)
    (hcomplete : E.CompleteEvidence (E.assessAt s) i s (E.wEnd s))
    (M : Finset (ℕ × ℕ))
    (hM : IsMaximalMatching ((E.assessInput s i).conflictGraph (E.assessInput s i).S) M) :
    let I := E.assessInput s i
    let F := I.Fof M
    let X := E.N.B \ F
    let K := I.U F \ X
    let Gs := persistG E.N s (E.wEnd s)
    ∀ f ∈ F,
      (nbrsIn Gs K f).card ≤ I.dout F f ∧
      I.dout F f ≤ (nbrsIn Gs K f).card + X.card ∧
      ((I.dout F f : ℕ) : ℤ) - ((E.P.t : ℤ) - I.mu - M.card) ≤ (((nbrsIn Gs K f).card : ℕ) : ℤ) := by sorry

end CharonChurn.Main
