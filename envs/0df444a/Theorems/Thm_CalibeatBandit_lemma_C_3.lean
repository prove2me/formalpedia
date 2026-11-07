-- Prove2me | Theorems.Thm_CalibeatBandit_lemma_C_3
-- name    : CalibeatBandit.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:02.436943+00:00
-- url     : https://prove2.me/theorems/a00c14ea-32c6-4b3e-a49e-d1953329efac
-- title:
--   Lemma C.3 — regret on corrected rewards is at most $(K\log K+\log 2)/\eta+2(e-2)\eta KT/(1-\mu)$
-- statement:
--   Assume $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, and consider any run of the interaction protocol driven by the bandit calibeating algorithm. Both
--   $$\mathbb E\Bigl[\max_f\sum_{t=1}^T\Bigl(\sum_ix_t(i)v_t(f(i))-\langle x_t,v_t\rangle\Bigr)\Bigr]\quad\text{and}\quad\mathbb E\Bigl[\max_f\sum_{t=1}^T\bigl(v_t(f(J_t))-\langle x_t,v_t\rangle\bigr)\Bigr]$$
--   are bounded by
--   $$\frac{K\log K+\log 2}{\eta}+\frac{2(e-2)\eta KT}{1-\mu},$$
--   where $f$ ranges over all maps $\mathcal A\to\mathcal A$.
--
--   This is the second part of the decomposition: the loss of the full-feedback reduction run on the corrected rewards $v_t$.
--
--   Differences from the source:
--   - encoding: the algorithm's quantities $x_t,p_t,v_t$ in an interaction satisfying the §2.1 protocol → `run.algX`, `run.algP`, `run.algV` along the realized history of a `ProtocolRun` driven by `calibeatPolicy K η μ`; reason: the run is the protocol of §2.1 (adaptive, randomized environment, $J_t\sim q_t$ and $I_t\sim p_t$ drawn by the learner); the policy reads only $J_{\le t}$, $I_{<t}$ and $y_s(I_s)$, $s<t$
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: the integrands are bounded measurable functions of the run, so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Lemma C.3, p.32 (PDF 32); proof pp.32–34

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Lemma C.3 (regret on corrected rewards).** Under the hypotheses of Theorem 3.2, in every
run of the bandit calibeating algorithm, both
`E[max_f ∑_{t=1}^T (∑_i x_t(i) v_t(f(i)) − ⟨x_t, v_t⟩)]` and `E[max_f ∑_{t=1}^T (v_t(f(J_t)) − ⟨x_t, v_t⟩)]`
are bounded by `(K log K + log 2)/η + 2(e − 2)ηKT/(1 − μ)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Lemma C.3, p.32.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. -/
theorem lemma_C_3 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (∑ i, run.algX η μ t ω i * run.algV η μ t ω (f i) - run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.algV η μ t ω (f (run.J t ω)) - run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) := by sorry

end CalibeatBandit
