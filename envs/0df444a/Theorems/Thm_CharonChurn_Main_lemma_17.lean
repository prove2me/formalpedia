-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_17
-- name    : CharonChurn.Main.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:57:51.628012+00:00
-- url     : https://prove2.me/theorems/eba366f0-a810-4a36-a8e5-8de90429fbb1
-- title:
--   Lemma 17 — the constructed graph is exact on the correct core
-- statement:
--   Throughout, $i$ is an eligible correct verifier for the window $[s,e]$, $e=s+\tau-1$ (correct, present throughout $[s,e+L_{\mathrm{flood}}]$, window inside the session current at round $e+L_{\mathrm{flood}}$), with complete target-window evidence at its assessment round $e+L_{\mathrm{flood}}$, in an execution satisfying all standing assumptions; all objects are computed from $i$'s retained evidence at that round. Let $M$ be any maximal matching of $C_0$, $F=S\cup V(M)$, $U=\hat V\setminus F$, $X=B\setminus F$, $K=U\setminus X$ and $G^*$ the persistent graph. Then $J[K]=G^*[K]$; for every $x\in X$ and $k\in K$, $\{x,k\}$ is an edge of $J$ iff it is an edge of $G^*$; consequently every pair of $U$ on which $J$ and $G^*$ disagree has both endpoints in $X$.
--
--   Differences from the source:
--   - reading: eligible correct verifier (assessing the window [s,e]) → i ∉ B, i present in every round of [s, e + L_flood] with e = s + τ − 1, and session(s) = session(e + L_flood); reason: §2.7 eligibility: present throughout [s_r, r] and the target window inside the session current at the assessment round r = e + L_flood
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 17, p. 28 (PDF 28)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Lemma 17 (The constructed graph is exact on the correct core), p. 28. With `F = S ∪ V(M)`
for a maximal matching `M` of `C₀`, `U = V* \ F`, `X = B \ F`, `K = U \ X`: `J[K] = G*[K]`;
every pair `{x, k}` with `x ∈ X`, `k ∈ K` is an edge of `J` iff it is an edge of `G*`; hence
every pair of `U` on which `J` and `G*` disagree has both endpoints in `X`. -/
theorem lemma_17 (E : Execution) (hE : E.Legal) (s i : ℕ)
    (helig : E.EligibleVerifier s i)
    (hcomplete : E.CompleteEvidence (E.assessAt s) i s (E.wEnd s))
    (M : Finset (ℕ × ℕ))
    (hM : IsMaximalMatching ((E.assessInput s i).conflictGraph (E.assessInput s i).S) M) :
    let I := E.assessInput s i
    let F := I.Fof M
    let X := E.N.B \ F
    let K := I.U F \ X
    let Gs := persistG E.N s (E.wEnd s)
    (∀ u ∈ K, ∀ v ∈ K, (I.J.Adj u v ↔ Gs.Adj u v)) ∧
    (∀ x ∈ X, ∀ k ∈ K, (I.J.Adj x k ↔ Gs.Adj x k)) ∧
    (∀ u ∈ I.U F, ∀ v ∈ I.U F, (I.J.Adj u v ↔ Gs.Adj u v) ∨ (u ∈ X ∧ v ∈ X)) := by sorry

end CharonChurn.Main
