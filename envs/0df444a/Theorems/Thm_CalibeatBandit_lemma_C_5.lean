-- Prove2me | Theorems.Thm_CalibeatBandit_lemma_C_5
-- name    : CalibeatBandit.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:13.973228+00:00
-- url     : https://prove2.me/theorems/e0481f10-1f7d-488b-949e-7f30bf3d55c0
-- title:
--   Lemma C.5 — correction loss is at most $(e-2)\eta KT/(1-\mu)$
-- statement:
--   Assume $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, and consider any run of the interaction protocol driven by the bandit calibeating algorithm. Then
--   $$\mathbb E\Bigl[\sum_{t=1}^T\langle x_t,v_t-y_t\rangle\Bigr]\le\frac{(e-2)\eta KT}{1-\mu}.$$
--
--   This is the price of the optimistic correction added to the importance-weighted estimates.
--
--   Differences from the source:
--   - encoding: the algorithm's quantities $x_t,p_t,v_t$ in an interaction satisfying the §2.1 protocol → `run.algX`, `run.algP`, `run.algV` along the realized history of a `ProtocolRun` driven by `calibeatPolicy K η μ`; reason: the run is the protocol of §2.1 (adaptive, randomized environment, $J_t\sim q_t$ and $I_t\sim p_t$ drawn by the learner); the policy reads only $J_{\le t}$, $I_{<t}$ and $y_s(I_s)$, $s<t$
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: the integrands are bounded measurable functions of the run, so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Lemma C.5, p.36 (PDF 36)

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Lemma C.5 (correction loss).** Under the hypotheses of Theorem 3.2, in every run of the
bandit calibeating algorithm, `E[∑_{t=1}^T ⟨x_t, v_t − y_t⟩] ≤ (e − 2)ηKT/(1 − μ)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Lemma C.5, p.36.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. -/
theorem lemma_C_5 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, ∑ t ∈ Finset.range T, run.algX η μ t ω ⬝ᵥ (run.algV η μ t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) := by sorry

end CalibeatBandit
