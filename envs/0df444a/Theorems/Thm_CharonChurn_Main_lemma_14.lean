-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_14
-- name    : CharonChurn.Main.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:57:45.235387+00:00
-- url     : https://prove2.me/theorems/67318f5e-4f9f-4d52-ad16-542d50563aab
-- title:
--   Lemma 14 — coverage implies exact instantaneous reconstruction
-- statement:
--   Let $i$ be a correct process present in round $r$. For every round $q$: if $i$'s retained evidence contains authenticated round-$q$ reports (bound to the active session) from at least $n-t$ distinct signer identities, then $W_i(q)=V_q$. Consequently, if this coverage holds for every round $q$ of $i$'s target window $[s,e]$, then $\hat V^{s,e}_i=\bigcap_{q=s}^eW_i(q)=\bigcap_{q=s}^eV_q=V^*$.
--
--   Differences from the source:
--   - generalization: a correct verifier and a target round q of its assessment → any round r at which correct i is present and any round q (the window of the second part is i's assessed window of round r); reason: specializes to target rounds at assessment; the coverage premise is unchanged (only n − t distinct authenticated signers, not complete correct evidence)
--   - reading: signatures existentially unforgeable against computationally bounded adversaries; results hold subject to this assumption (§2.5) → hypothesis E.NoForgery: every adversary-supplied record (initial or joining cache, Byzantine message) that verifies under a non-Byzantine identity carries that identity's genuine canonical report for a round in which it is present; reason: the source's correctness is conditional on signature security; this is that conditional abstraction, stated openly rather than as a cryptographic claim
--   - encoding: history-adaptive topology, churn and Byzantine adversary; arbitrary initial mutable states → universal quantification over all network sequences, all Byzantine message functions and all initial/joining caches; reason: the protocol is deterministic, so every adaptive strategy induces one such sequence; same set of executions
--   - reading: the prescribed maximum report encoding length (§3.1), with the same envelope bound for malformed records (§3.7) → the full binary record length is bounded by Crypto.maxReportBits(session, original round); ReportsFit requires each correct generated report to fit that public bound; reason: the source leaves the numerical format limit unspecified but uses it for whole envelopes; parameterizing it by signed context permits unbounded future identity and round encodings, while fixing the limit for every copy of a report; this asserts format compatibility, not delivery or complete evidence
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 14, p. 26 (PDF 26)

import Mathlib
import Definitions.Def_CharonChurn_Main_Execution

namespace CharonChurn.Main

/-- Lemma 14 (Coverage implies exact instantaneous reconstruction), p. 26. At a correct
verifier `i` in round `r`: if it holds authenticated round-`q` reports from at least `n − t`
distinct signers then `W_i(q) = V_q`; hence if coverage holds for every round of its target
window `[s, e]`, then `V̂ = ⋂ W_i(q) = ⋂ V_q = V*`. -/
theorem lemma_14 (E : Execution) (hE : E.Legal) (r i : ℕ) (hi : i ∈ correctSet E.N r) :
    (∀ q, (E.P.n : ℤ) - E.P.t ≤ (((E.inputAt r i).R q).card : ℤ) →
      (E.inputAt r i).W q = E.N.V q) ∧
    ((∀ q ∈ (E.inputAt r i).window, (E.P.n : ℤ) - E.P.t ≤ (((E.inputAt r i).R q).card : ℤ)) →
      (E.inputAt r i).Vhat = persistV E.N (E.winStart r) (E.winEnd r)) := by sorry

end CharonChurn.Main
