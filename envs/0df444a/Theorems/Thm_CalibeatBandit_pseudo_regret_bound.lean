-- Prove2me | Theorems.Thm_CalibeatBandit_pseudo_regret_bound
-- name    : CalibeatBandit.pseudo_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:04.799933+00:00
-- url     : https://prove2.me/theorems/03e8548e-d7ea-4b0e-812e-33372b720d5e
-- title:
--   Proof of Theorem 3.2 (p.36) — $\mathbb E[R^{a,p}_T]\le r_T$ for $a\in\{\mathrm{SR},\mathrm{Rec}\}$
-- statement:
--   Assume $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, and consider any run of the interaction protocol driven by the bandit calibeating algorithm, with $p_t$ the mixed strategy it plays. Then
--   $$\mathbb E\bigl[R^{\mathrm{SR},p}_T\bigr]\le r_T\qquad\text{and}\qquad\mathbb E\bigl[R^{\mathrm{Rec},p}_T\bigr]\le r_T,\qquad r_T=\mu T+\frac{2K\log K+\log 2}{\eta}+\frac{5\eta KT}{1-\mu}.$$
--
--   It combines the decomposition of §C.2 with Lemmas C.3–C.5 and $3(e-2)<5$.
--
--   Differences from the source:
--   - encoding: the algorithm's quantities $x_t,p_t,v_t$ in an interaction satisfying the §2.1 protocol → `run.algX`, `run.algP`, `run.algV` along the realized history of a `ProtocolRun` driven by `calibeatPolicy K η μ`; reason: the run is the protocol of §2.1 (adaptive, randomized environment, $J_t\sim q_t$ and $I_t\sim p_t$ drawn by the learner); the policy reads only $J_{\le t}$, $I_{<t}$ and $y_s(I_s)$, $s<t$
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: the integrands are bounded measurable functions of the run, so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, proof of Theorem 3.2, p.36 (PDF 36)

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rT

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **The pseudo regrets are at most `r_T`** (§C.2, proof of Theorem 3.2, p.36). Under the
hypotheses of Theorem 3.2, in every run of the bandit calibeating algorithm, for both
`a ∈ {SR, Rec}`, `E[R^{a,p}_T] ≤ μT + (2K log K + log 2)/η + 5ηKT/(1 − μ) = r_T`, where
`R^{SR,p}_T = max_f ∑_t (∑_i p_t(i) y_t(f(i)) − ⟨p_t, y_t⟩)` and
`R^{Rec,p}_T = max_f ∑_t (y_t(f(J_t)) − ⟨p_t, y_t⟩)` (§C.1, p.30).

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, proof of Theorem 3.2, p.36.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. `p_t` is the mixed strategy the algorithm plays. -/
theorem pseudo_regret_bound {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, pseudoSwapRegret T (fun t => run.algP η μ t ω) (fun t => run.y t ω) ∂P ≤ rT K T η μ ∧
    ∫ ω, pseudoRewardLoss T (fun t => run.algP η μ t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P ≤ rT K T η μ := by sorry

end CalibeatBandit
