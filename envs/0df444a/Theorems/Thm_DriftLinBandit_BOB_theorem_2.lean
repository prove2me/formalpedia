-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_theorem_2
-- name    : DriftLinBandit.BOB.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:06.761004+00:00
-- url     : https://prove2.me/theorems/9645b8e5-47ce-43c1-955c-32c29a3462e6
-- title:
--   Theorem 2, p. 10 — SW-RLSE confidence bound |xᵀ(θ̂_t − θ_t)| ≤ L∑‖θ_s − θ_{s+1}‖ + β‖x‖_{V_{t−1}^{−1}} for all x ∈ D_t
-- statement:
--   Consider a drifting linear bandit instance satisfying the standing assumptions ($\|X\|_2\le L$, $|\langle X,\theta_t\rangle|\le1$, $\|\theta_t\|_2\le S$) and Assumption 1, with i.i.d. centred $R$-sub-Gaussian noises and non-anticipatory actions $X_s\in D_s$ with rewards $Y_s=\langle X_s,\theta_s\rangle+\eta_s$. Let $\lambda>0$, $w\ge1$, and let $\hat\theta_t=V_{t-1}^{-1}\sum_{s=1\vee(t-w)}^{t-1}X_sY_s$ be the sliding-window estimate (2) and $\beta$ the radius (3). Then for every $t\in[T]$ and $\delta\in(0,1]$, with probability at least $1-\delta$,
--   $$
--   \big|x^\top(\hat\theta_t-\theta_t)\big|\le L\sum_{s=1\vee(t-w)}^{t-1}\|\theta_s-\theta_{s+1}\|_2+\beta\,\|x\|_{V_{t-1}^{-1}}\qquad\text{for all }x\in D_t .
--   $$
--
--   This confidence bound is what the UCB rule (5) of SW-UCB is built on, and it drives the regret analysis of Theorem 3.
--
--   **Formalization Note.** The quantifier "for all $x\in D_t$" sits inside the probability: the event bounded by $\delta$ is that some $x\in D_t$ violates the inequality. As for Lemma 4, $d\ge2$ and $\delta>0$ are added hypotheses (the claim fails numerically at $d=1$).
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 10, Theorem 2; Assumption 1, p. 10

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open MeasureTheory Matrix

/-- Theorem 2 (p. 10). Under the standing assumptions and Assumption 1, with i.i.d. centred
`R`-sub-Gaussian noise and non-anticipatory actions `X_s ∈ D_s` with rewards
`Y_s = ⟨X_s, θ_s⟩ + η_s`, for any round `t ∈ [T]`, any window size `w ≥ 1` and any `δ ∈ (0, 1]`,
with probability at least `1 − δ` the sliding-window estimate `θ̂_t` of (2) satisfies, for all
`x ∈ D_t` simultaneously,
`|xᵀ(θ̂_t − θ_t)| ≤ L ∑_{s=1∨(t−w)}^{t−1} ‖θ_s − θ_{s+1}‖₂ + β ‖x‖_{V_{t−1}^{−1}}`,
with `β` as in (3). Stated for `d ≥ 2` (the printed radius is too small at `d = 1`). -/
theorem theorem_2 {d : ℕ} (hd : 2 ≤ d) (I : Instance d) (R L S lam : ℝ) (hR : 0 < R)
    (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam) (hst : I.Standing L S) (hA : Assumption1 I)
    (w : ℕ) (hw : 1 ≤ w)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (hη : IsSubGNoise P η R)
    (X : ℕ → Ω → (Fin d → ℝ)) (hXD : ∀ s ∈ Finset.Icc 1 I.T, ∀ ω, X s ω ∈ I.D s)
    (hX : IsPredictable η X) (t : ℕ) (ht : t ∈ Finset.Icc 1 I.T) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    P {ω | ∃ x ∈ I.D t,
        L * ∑ s ∈ win 1 w t, l2 (I.θ s - I.θ (s + 1)) +
            beta R L S lam d w δ * wnorm (gram lam (fun s => X s ω) (win 1 w t)) x <
          |x ⬝ᵥ (est lam (fun s => X s ω) (fun s => X s ω ⬝ᵥ I.θ s + η s ω) (win 1 w t) -
            I.θ t)|} ≤ ENNReal.ofReal δ := by sorry

end DriftLinBandit.BOB
