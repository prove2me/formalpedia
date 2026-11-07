-- Prove2me | Theorems.Thm_CalibeatBandit_eq_C_1
-- name    : CalibeatBandit.eq_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:50.474712+00:00
-- url     : https://prove2.me/theorems/6b062e4e-68d3-4922-8bcd-495745da1fdb
-- title:
--   Eq. (C.1) — the mixing feedback $\sum_tH^{\mathrm{SR}}_t$ telescopes (with the $\mathrm{Rec}$ analogue)
-- statement:
--   For the bandit calibeating algorithm with learning rate $\eta>0$ (any exploration parameter $\mu$) and every history of recommended actions, played actions and observed rewards,
--   $$\sum_{t=1}^TH^{\mathrm{SR}}_t=\frac1\eta\sum_i\log\Bigl(\frac1K\sum_j\exp\Bigl(\eta\sum_{t=1}^Tx_t(i)v_t(j)\Bigr)\Bigr)$$
--   and
--   $$\sum_{t=1}^TH^{\mathrm{Rec}}_t=\frac1\eta\sum_i\log\Bigl(\frac1K\sum_j\exp\Bigl(\eta\sum_{t=1}^T\mathbb 1\{J_t=i\}\,v_t(j)\Bigr)\Bigr).$$
--
--   Because each internal learner is exponential weights started from uniform weights, the per-round feedback is a difference of log-partition functions and the sum telescopes. The identity drives the bound on the regret on corrected rewards (Lemma C.3).
--
--   Differences from the source:
--   - generalization: the identity for $\sum_tH^{\mathrm{SR}}_t$ of the algorithm → the identity for every history and every $\mu$, together with the analogous identity for $\sum_tH^{\mathrm{Rec}}_t$; reason: the telescoping uses only the exponential-weights update; the Rec identity is the one the paper's "similar" analysis of the second term of Lemma C.3 uses
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, display (C.1), p.32 (PDF 32); the Rec identity is the analysis of the second term of Lemma C.3 ("similar", p.32)

import Mathlib
import Definitions.Def_CalibeatBandit_algState

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **(C.1): the mixing learner's `SR` feedback telescopes** (§C.2, proof of Lemma C.3,
p.32). For the bandit calibeating algorithm with learning rate `η > 0` and every history,
`∑_{t=1}^T H^SR_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T x_t(i) v_t(j)))`,
and likewise
`∑_{t=1}^T H^Rec_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T 1{J_t = i} v_t(j)))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.1), p.32; the `Rec` identity is the "similar" analysis of the
second term of Lemma C.3 (p.32).

**Formalization Note.** `algHSR`, `algHRec`, `algX`, `algV` are the algorithm's `H^SR_t`,
`H^Rec_t`, `x_t`, `v_t` computed from the learner's observations `J`, `I` and observed rewards
`r` (any sequences); rounds are `0, …, T − 1`; `log` is `Real.log`. The identity is exact for every
history and every exploration parameter `μ`. The second conjunct is the `Rec` analogue that the
paper uses without displaying it. -/
theorem eq_C_1 {K : ℕ} (η μ : ℝ) (hη : 0 < η) (J I : ℕ → Fin K) (r : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, algHSR η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, algX η μ J I r t i * algV η μ J I r t j)) ∧
    ∑ t ∈ Finset.range T, algHRec η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, (if J t = i then algV η μ J I r t j else 0))) := by sorry

end CalibeatBandit
