-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_4_1
-- name    : CommThresholdPR.StrongConverse.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:51.07491+00:00
-- url     : https://prove2.me/theorems/c82df068-65cf-417f-a308-1d0881ada755
-- title:
--   Lemma 4.1 — a small successful conditioning set
-- statement:
--   In the deterministic experiment of Construction 4.1 on $n\ge1$ copies, let $W_i$ denote coordinate success and suppose the simultaneous success probability is at least $0<p\le1$. For $0<\varepsilon<1$, there is $S\subseteq[n]$ satisfying all three bounds:
--   $$|S|\le\frac{\log_2(1/p)}{-\log_2(1-\varepsilon)},\qquad P(W_S)\ge p,\qquad P(W_i\mid W_S)\ge1-\varepsilon\quad(i\in[n]).$$
--   Here $W_S=\bigcap_{i\in S}W_i$. The set can be empty, and $p>0$ ensures that the displayed conditioning is meaningful. This supplies the chosen set in Construction 4.1; its existence is a conclusion.
--
--   Differences from the source:
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 4.1, p. 13, (26), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_4_1 {n : ℕ} (hn : 0 < n) (e : Extraction X Y A B n)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hsuccess : p ≤ prob e.P (fun z => ∀ i, e.wins i z)) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≤ Real.logb 2 (1 / p) / (-Real.logb 2 (1 - ε)) ∧
      p ≤ prob e.P (e.winsSet S) ∧
      ∀ i, 1 - ε ≤ cprob e.P (e.wins i) (e.winsSet S) := by sorry

end CommThresholdPR.StrongConverse
