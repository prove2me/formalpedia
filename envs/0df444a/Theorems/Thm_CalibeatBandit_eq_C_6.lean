-- Prove2me | Theorems.Thm_CalibeatBandit_eq_C_6
-- name    : CalibeatBandit.eq_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:54.426667+00:00
-- url     : https://prove2.me/theorems/4aa54293-03f0-4f50-8f9e-8a3f6bb124d1
-- title:
--   Eq. (C.6) — $\mathbb E[\sum_jx_t(j)v_t(j)^2\mid\mathcal O_{t-1}]\le2K/(1-\mu)$
-- statement:
--   Assume $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, and consider any run of the interaction protocol driven by the bandit calibeating algorithm. Let $\mathcal O_{t-1}$ be the information immediately before $I_t$ is sampled. Then for every round $t\le T$,
--   $$\mathbb E\Bigl[\sum_jx_t(j)v_t(j)^2\Bigm|\mathcal O_{t-1}\Bigr]=\sum_j\frac{x_t(j)}{p_t(j)}\Bigl(y_t(j)^2+2(e-2)\eta y_t(j)+\frac{(e-2)^2\eta^2}{p_t(j)}\Bigr)\le2\sum_j\frac{x_t(j)}{p_t(j)}\le\frac{2K}{1-\mu},$$
--   the equality holding almost surely and the inequalities for every outcome.
--
--   This bounds the variance term of (C.5) by propensity scoring: $\mathbb E[\hat y_t(j)\mid\mathcal O_{t-1}]=y_t(j)$ and $\mathbb E[\hat y_t(j)^2\mid\mathcal O_{t-1}]=y_t(j)^2/p_t(j)$.
--
--   **Formalization Note** $\mathcal O_{t-1}$ is `run.preDraw t` $=\mathcal E_t\vee\sigma(J_t)$.
--
--   Differences from the source:
--   - encoding: the algorithm's quantities $x_t,p_t,v_t$ in an interaction satisfying the §2.1 protocol → `run.algX`, `run.algP`, `run.algV` along the realized history of a `ProtocolRun` driven by `calibeatPolicy K η μ`; reason: the run is the protocol of §2.1 (adaptive, randomized environment, $J_t\sim q_t$ and $I_t\sim p_t$ drawn by the learner); the policy reads only $J_{\le t}$, $I_{<t}$ and $y_s(I_s)$, $s<t$
--   - encoding: $\mathcal O_{t-1}$, "all information immediately before sampling $I_t$" → `run.preDraw t` $=\mathcal E_t\vee\sigma(J_t)$; reason: this is the σ-algebra the protocol conditions the draw of $I_t$ on
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, display (C.6), p.34 (PDF 34)

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **(C.6): the conditional second moment of the corrected estimates** (§C.2, proof of
Lemma C.3, p.34). In every run of the bandit calibeating algorithm under the hypotheses of
Theorem 3.2, for every round `t`, with `𝒪_{t−1}` the information immediately before `I_t` is sampled,
`E[∑_j x_t(j) v_t(j)² | 𝒪_{t−1}] = ∑_j (x_t(j)/p_t(j)) (y_t(j)² + 2(e − 2)ηy_t(j) + (e − 2)²η²/p_t(j))
  ≤ 2 ∑_j x_t(j)/p_t(j) ≤ 2K/(1 − μ)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.6), p.34.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. `𝒪_{t−1}` is `run.preDraw t = info t ⊔ σ(J_t)` (p.31: "all
information immediately before sampling I_t"); the equality holds `P`-almost surely, the two
inequalities for every outcome. -/
theorem eq_C_6 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) (t : ℕ) (ht : t < T) :
    condExp (run.preDraw t) P (fun ω => ∑ j, run.algX η μ t ω j * run.algV η μ t ω j ^ 2)
      =ᵐ[P] (fun ω => ∑ j, run.algX η μ t ω j / run.algP η μ t ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / run.algP η μ t ω j)) ∧
    (∀ ω, ∑ j, run.algX η μ t ω j / run.algP η μ t ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / run.algP η μ t ω j) ≤ 2 * ∑ j, run.algX η μ t ω j / run.algP η μ t ω j) ∧
    (∀ ω, 2 * ∑ j, run.algX η μ t ω j / run.algP η μ t ω j ≤ 2 * K / (1 - μ)) := by sorry

end CalibeatBandit
