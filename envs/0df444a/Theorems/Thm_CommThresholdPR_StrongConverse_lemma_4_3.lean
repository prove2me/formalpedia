-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_4_3
-- name    : CommThresholdPR.StrongConverse.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:03.814995+00:00
-- url     : https://prove2.me/theorems/861f8753-1146-45a4-a005-4fd23d13d6f7
-- title:
--   Lemma 4.3 — all properties of the extracted law
-- statement:
--   For the actual law $q$ of Construction 4.1 with $n\ge1$, rate $R\ge0$, success lower bound $0<p\le1$ and $0<\varepsilon<1$, all four properties hold:
--   $$\operatorname{err}(q)\le\varepsilon,\qquad D(q_{XY}\|\mu)\le\frac{\log_2(1/p)}n,$$
--   $$I_q(X;V\mid Y)+I_q(Y;V\mid X)\le R+\frac{\log_2(1/p)}n\left(2+\frac{L_{\rm out}}{-\log_2(1-\varepsilon)}\right),$$
--   $$q(a,b\mid x,y,v)=q(a\mid x,v)q(b\mid y,v)$$
--   at every positive-probability conditioning value. Here $L_{\rm out}=\log_2(|A||B|)$. Error is the failure event for $g$, and divergence is extended-real. These are conclusions about the constructed law, not conditions defining $q$.
--
--   Differences from the source:
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
--   - encoding: finite joint laws, base-two information and conditioning at positive-probability values → Mathlib PMF laws, finite entropy differences and explicit positive-probability conditional rows; reason: the representation changes no finite distribution; support mismatches retain infinite divergence and null conditional rows are used only as arbitrary normalized fallbacks
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 4.3, p. 15; (22)–(24), p. 12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_4_3 {n : ℕ} (hn : 0 < n) (e : Extraction X Y A B n)
    (R p ε : ℝ) (hsetup : e.Setup R p ε) :
    lawError e.g (e.q hn) ≤ ε ∧
    divergence ((e.q hn).map (fun z => (z.x,z.y))) e.μ ≤
      ((Real.logb 2 (1 / p) / n : ℝ) : EReal) ∧
    infoSum (e.q hn) ≤ R + Real.logb 2 (1 / p) / n *
      (2 + logOutput A B / (-Real.logb 2 (1 - ε))) ∧
    localOutputs (e.q hn) := by sorry

end CommThresholdPR.StrongConverse
