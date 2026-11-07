-- Prove2me | Theorems.Thm_CalibeatBandit_sampling_conversion_C_1
-- name    : CalibeatBandit.sampling_conversion_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:08.647377+00:00
-- url     : https://prove2.me/theorems/43a1668e-66ae-4e5b-8aaf-ec081391b4d8
-- title:
--   §C.1 (p.31) — sampling conversion $\mathbb E[\mathrm{SR}_T]\le\mathbb E[R^{\mathrm{SR},p}_T]+\sqrt{2TK\log K}$
-- statement:
--   Consider any learner and any run of the interaction protocol with $K\ge1$ actions, with $p_t$ the learner's mixed strategy in round $t$. Then
--   $$\mathbb E[\mathrm{SR}_T]\le\mathbb E\bigl[R^{\mathrm{SR},p}_T\bigr]+\sqrt{2TK\log K}.$$
--
--   Since $I_t$ has conditional law $p_t$ given the information before it is sampled, the differences $D_t(f)=y_t(f(I_t))-y_t(I_t)-\sum_ip_t(i)(y_t(f(i))-y_t(i))$ have conditional mean zero and $|D_t(f)|\le2$; Hoeffding's lemma and a union over the $K^K$ maps $f$ give the $\sqrt{2TK\log K}$ term.
--
--   **Formalization Note** $p_t$ is `run.played t`.
--
--   Differences from the source:
--   - generalization: the learner of Algorithm 1 (and, by the proof of Theorem 3.2, the bandit algorithm) → every learner policy; reason: the argument uses only that $I_t$ has conditional law $p_t$ given $\mathcal O_{t-1}$ and $y_t\in[0,1]^K$; both algorithms are instances
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: in every run the integrands are bounded and almost everywhere measurable (the conditional law pins $p_t$ a.s.), so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ → the explicit hypothesis $0<K$; reason: the paper states this once, on p.7; no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.1, proof of Lemma C.1, p.31 (PDF 31); reused in the proof of Theorem 3.2, p.36

import Mathlib
import Definitions.Def_CalibeatBandit_ProtocolRun
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Sampling conversion from pseudo swap regret to swap regret** (§C.1, proof of Lemma C.1,
p.31). In every run of the §2.1 protocol with `K ≥ 1` actions, with `p_t` the learner's mixed
strategy, `E[SR_T] ≤ E[R^{SR,p}_T] + √(2TK log K)`, where
`R^{SR,p}_T = max_f ∑_t (∑_i p_t(i) y_t(f(i)) − ⟨p_t, y_t⟩)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.1, proof of Lemma C.1, p.31; reused in the proof of Theorem 3.2, p.36.

**Formalization Note.** Stated for an arbitrary learner `policy`; `p_t` is `run.played t`, and
`I_t` has conditional law `p_t` given `𝒪_{t−1} = info t ⊔ σ(J_t)` by the protocol. Rounds are
`0, …, T − 1`; `log` is `Real.log`; `E` is the Bochner integral. -/
theorem sampling_conversion_C_1 {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (policy : Policy K) (run : ProtocolRun K T P policy) (hK : 0 < K) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
      ≤ ∫ ω, pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) ∂P + Real.sqrt (2 * T * K * Real.log K) := by sorry

end CalibeatBandit
