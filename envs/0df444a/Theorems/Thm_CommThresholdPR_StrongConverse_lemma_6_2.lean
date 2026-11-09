-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_6_2
-- name    : CommThresholdPR.StrongConverse.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:08.620699+00:00
-- url     : https://prove2.me/theorems/e5a41c3e-bb4a-4715-a611-9df2f8e295f7
-- title:
--   Lemma 6.2 — a zero-message protocol on the original input law
-- statement:
--   In the standing setup of Construction 4.1, there is a zero-message protocol $\sigma$ on the original law $\mu$ with $\operatorname{IC}_{\mu}(\sigma)=0$ and
--   $$\operatorname{err}_{\mu}(\sigma)\le\varepsilon+\delta(n,p)+2\sqrt{(\ln2)\left[R+\frac{\log_2(1/p)}n\left(2+\frac{L_{\rm out}}{-\log_2(1-\varepsilon)}\right)\right]}.$$
--   All terms in (44) are retained. This statement requires the standing positive $n,p$ and $0<\varepsilon<1$, but no small-$\delta$ condition. It provides a protocol that can meet the zero information budget.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 6.2, p. 21, (44), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_6_2 {n : ℕ} (hn : 0 < n) (e : Extraction X Y A B n)
    (R p ε : ℝ) (hsetup : e.Setup R p ε) :
    ∃ σ : Protocol X Y A B, σ.cost = 0 ∧ σ.info e.μ = 0 ∧
      protocolError e.g e.μ σ ≤ ε + delta n p + 2 * Real.sqrt (Real.log 2 *
        (R + Real.logb 2 (1 / p) / n *
          (2 + logOutput A B / (-Real.logb 2 (1 - ε))))) := by sorry

end CommThresholdPR.StrongConverse
