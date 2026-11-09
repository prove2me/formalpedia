-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_4_2
-- name    : CommThresholdPR.StrongConverse.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:26.526134+00:00
-- url     : https://prove2.me/theorems/88c288bb-f499-4ddf-ae67-2a83526d5829
-- title:
--   Lemma 4.2 — conditioned coordinate outputs remain local
-- statement:
--   Under the standing setup of Construction 4.1, for every coordinate $i$, let $Q=P(\cdot\mid W_S)$ and $V_i=(X_{<i},Y_{>i},\overline T)$. At every conditioning value of positive $Q$ probability,
--   $$Q(A_i,B_i\mid X_i,Y_i,V_i)=Q(A_i\mid X_i,V_i)Q(B_i\mid Y_i,V_i).$$
--   The law is computed from the source deterministic protocol and its chosen successful-coordinate event. The factorization is a conclusion, including when $i\in S$ and its outputs were already revealed.
--
--   Differences from the source:
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
--   - encoding: finite joint laws, base-two information and conditioning at positive-probability values → Mathlib PMF laws, finite entropy differences and explicit positive-probability conditional rows; reason: the representation changes no finite distribution; support mismatches retain infinite divergence and null conditional rows are used only as arbitrary normalized fallbacks
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 4.2, p. 14, (29), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_4_2 {n : ℕ} (hn : 0 < n) (e : Extraction X Y A B n)
    (R p ε : ℝ) (hsetup : e.Setup R p ε) :
    ∀ i, localOutputs (e.coordinate i) := by sorry

end CommThresholdPR.StrongConverse
