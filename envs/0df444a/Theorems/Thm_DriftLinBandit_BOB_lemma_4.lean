-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_lemma_4
-- name    : DriftLinBandit.BOB.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:56.439208+00:00
-- url     : https://prove2.me/theorems/29612bac-583f-4d75-82f8-61d74882f9fa
-- title:
--   Lemma 4, p. 36 — sliding-window self-normalized bound ‖∑η_sX_s − λθ_t‖_{V_{t−1}^{−1}} ≤ β with probability ≥ 1 − δ
-- statement:
--   Consider a drifting linear bandit instance with $\|X\|_2\le L$ on every $D_t$ and $\|\theta_t\|_2\le S$, noises $\eta_t$ that are i.i.d., centred and $R$-sub-Gaussian, and non-anticipatory actions $X_s\in D_s$. Let $\lambda>0$, $w\ge1$ and $V_{t-1}=\lambda I+\sum_{s=1\vee(t-w)}^{t-1}X_sX_s^\top$. Then for every round $t\in[T]$ and every $\delta\in(0,1]$, with probability at least $1-\delta$,
--   $$
--   \Big\|\sum_{s=1\vee(t-w)}^{t-1}\eta_sX_s-\lambda\theta_t\Big\|_{V_{t-1}^{-1}}\le R\sqrt{d\ln\Big(\frac{1+wL^2/\lambda}{\delta}\Big)}+\sqrt\lambda\,S .
--   $$
--
--   This is the sliding-window form of the self-normalized bound of Abbasi-Yadkori, Pál and Szepesvári (2011); it controls the noise term of the decomposition (34).
--
--   **Formalization Note.** The statement bounds the probability of the complementary event by $\delta$. Two hypotheses are added to the page: $d\ge2$, because at $d=1$ the printed radius is smaller than the self-normalized bound requires and the claim fails numerically; and $\delta>0$ (the page allows $\delta\in[0,1]$, where $\delta=0$ makes the logarithm meaningless). Non-anticipation is encoded by requiring $X_s$ to be a measurable function of $\eta_0,\dots,\eta_{s-1}$.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 36, Lemma 4 (Appendix B)

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open MeasureTheory Matrix

/-- Lemma 4 (p. 36, after Abbasi-Yadkori et al. 2011). Let the noise be i.i.d. centred
`R`-sub-Gaussian, the instance satisfy the standing bounds `‖X‖₂ ≤ L`, `‖θ_t‖₂ ≤ S`, and the actions
`X_s ∈ D_s` be non-anticipatory. Then for any round `t ∈ [T]`, any window size `w ≥ 1` and any
`δ ∈ (0, 1]`, with probability at least `1 − δ`,
`‖∑_{s=1∨(t−w)}^{t−1} η_s X_s − λθ_t‖_{V_{t−1}^{−1}} ≤ R √(d ln((1 + wL²/λ)/δ)) + √λ S`.
Stated for `d ≥ 2` (the printed radius is too small at `d = 1`). -/
theorem lemma_4 {d : ℕ} (hd : 2 ≤ d) (I : Instance d) (R L S lam : ℝ) (hR : 0 < R)
    (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam) (hst : I.Standing L S) (w : ℕ) (hw : 1 ≤ w)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (hη : IsSubGNoise P η R)
    (X : ℕ → Ω → (Fin d → ℝ)) (hXD : ∀ s ∈ Finset.Icc 1 I.T, ∀ ω, X s ω ∈ I.D s)
    (hX : IsPredictable η X) (t : ℕ) (ht : t ∈ Finset.Icc 1 I.T) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    P {ω | beta R L S lam d w δ <
        wnorm (gram lam (fun s => X s ω) (win 1 w t))
          ((∑ s ∈ win 1 w t, η s ω • X s ω) - lam • I.θ t)} ≤ ENNReal.ofReal δ := by sorry

end DriftLinBandit.BOB
