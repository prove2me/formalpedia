-- Prove2me | Theorems.Thm_CalibeatBandit_lemma_C_4
-- name    : CalibeatBandit.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:03.590061+00:00
-- url     : https://prove2.me/theorems/3333d5bb-e445-49d0-9f51-8134fb2fba8e
-- title:
--   Lemma C.4 — estimation loss is at most $K\log K/\eta$
-- statement:
--   Assume $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, and consider any run of the interaction protocol driven by the bandit calibeating algorithm. Both
--   $$\mathbb E\Bigl[\max_f\sum_{t=1}^T\sum_ix_t(i)\bigl(y_t(f(i))-v_t(f(i))\bigr)\Bigr]\quad\text{and}\quad\mathbb E\Bigl[\max_f\sum_{t=1}^T\bigl(y_t(f(J_t))-v_t(f(J_t))\bigr)\Bigr]$$
--   are bounded by $\dfrac{K\log K}{\eta}$, where $f$ ranges over all maps $\mathcal A\to\mathcal A$.
--
--   The optimistic correction $(e-2)\eta/p_t(j)$ in $v_t$ makes $\exp(\eta\sum_t\cdots)$ a supermartingale for each fixed $f$, and the $K^K$ rules give the $K\log K/\eta$.
--
--   Differences from the source:
--   - encoding: the algorithm's quantities $x_t,p_t,v_t$ in an interaction satisfying the §2.1 protocol → `run.algX`, `run.algP`, `run.algV` along the realized history of a `ProtocolRun` driven by `calibeatPolicy K η μ`; reason: the run is the protocol of §2.1 (adaptive, randomized environment, $J_t\sim q_t$ and $I_t\sim p_t$ drawn by the learner); the policy reads only $J_{\le t}$, $I_{<t}$ and $y_s(I_s)$, $s<t$
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: the integrands are bounded measurable functions of the run, so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Lemma C.4, p.35 (PDF 35)

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Lemma C.4 (estimation loss).** Under the hypotheses of Theorem 3.2, in every run of the
bandit calibeating algorithm, both
`E[max_f ∑_{t=1}^T ∑_i x_t(i)(y_t(f(i)) − v_t(f(i)))]` and `E[max_f ∑_{t=1}^T (y_t(f(J_t)) − v_t(f(J_t)))]`
are bounded by `K log K/η`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Lemma C.4, p.35.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. -/
theorem lemma_C_4 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, ∑ i, run.algX η μ t ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))) ∂P
      ≤ K * Real.log K / η ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.y t ω (f (run.J t ω)) - run.algV η μ t ω (f (run.J t ω)))) ∂P
      ≤ K * Real.log K / η := by sorry

end CalibeatBandit
