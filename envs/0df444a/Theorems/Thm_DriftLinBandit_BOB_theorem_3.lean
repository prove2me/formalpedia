-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_theorem_3
-- name    : DriftLinBandit.BOB.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:56.448733+00:00
-- url     : https://prove2.me/theorems/ba7d2ba5-331a-4ae9-9ef5-5ef5e4f9d1b2
-- title:
--   Theorem 3, pp. 11–12 — SW-UCB has dynamic regret Õ(wB_T + dT/√w)
-- statement:
--   Fix positive constants $R,L,S,\lambda$ with $\lambda S^2\ge1$. There are constants $C>0$ and $k\in\mathbb N$, depending only on $R,L,S,\lambda$, with the following property. For every dimension $d\ge1$, every drifting linear bandit instance with horizon $T\ge1$ that satisfies the standing assumptions and Assumption 1, every $B_T\ge0$ with $\sum_{t=1}^{T-1}\|\theta_{t+1}-\theta_t\|_2\le B_T$, every window size $1\le w\le T$, and every i.i.d. centred $R$-sub-Gaussian noise, the SW-UCB algorithm (Algorithm 1) with window $w$, regularisation $\lambda$ and $\delta=1/T$ in its radius has integrable regret and
--   $$
--   \mathcal R_T(\text{SW-UCB})\le C\,(1+\ln(dT))^k\Big(wB_T+\frac{dT}{\sqrt w}\Big),
--   $$
--   that is, $\mathcal R_T(\text{SW-UCB})=\widetilde O(wB_T+dT/\sqrt w)$.
--
--   Tuning $w$ to $B_T$ gives the minimax rate $\widetilde O(d^{2/3}B_T^{1/3}T^{2/3})$; BOB (Proposition 1) applies this bound block by block.
--
--   **Formalization Note.** $\widetilde O$ is read as the existence of $C,k$ fixed before $d$, $T$, $B_T$, the instance and the noise. $\lambda S^2\ge1$ and $\delta=1/T$ are the choices made in the paper's proof (Appendix C, pp. 36 and 39). $B_T$ is any upper bound on the variation rather than the regime $B_T=\Theta(T^\rho)$. $w\le T$ is added: without it the bound fails ($dT/\sqrt w\to0$ as $w\to\infty$). Only the first sentence of Theorem 3 is formalized; the tuned-window corollaries are not.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, pp. 11–12, Theorem 3 (first sentence); Appendix C, pp. 36–39

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open MeasureTheory

/-- Theorem 3 (pp. 11–12), first sentence: the dynamic regret of SW-UCB is `Õ(w B_T + dT/√w)`.
For all positive `R, L, S, λ` with `λS² ≥ 1` there are constants `C > 0` and `k` (depending only on
`R, L, S, λ`) such that for every dimension `d ≥ 1`, every instance with horizon `T ≥ 1` satisfying
the standing assumptions and Assumption 1, every variation budget `B ≥ 0` with
`∑_{t=1}^{T−1} ‖θ_{t+1} − θ_t‖₂ ≤ B`, every window size `1 ≤ w ≤ T` and every i.i.d. centred
`R`-sub-Gaussian noise, SW-UCB with window `w` and `δ = 1/T` has integrable regret and
`R_T(SW-UCB) ≤ C (1 + ln(dT))^k (w B + dT/√w)`. -/
theorem theorem_3 (R L S lam : ℝ) (hR : 0 < R) (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam)
    (hlamS : 1 ≤ lam * S ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (d : ℕ), 1 ≤ d → ∀ (I : Instance d), 1 ≤ I.T → I.Standing L S → Assumption1 I →
      ∀ (B : ℝ), 0 ≤ B → variation I ≤ B →
      ∀ (w : ℕ), 1 ≤ w → w ≤ I.T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), IsSubGNoise P η R →
        Integrable (regret I (swucb I R L S lam w (1 / (I.T : ℝ)) 1 η)) P ∧
        ∫ ω, regret I (swucb I R L S lam w (1 / (I.T : ℝ)) 1 η) ω ∂P ≤
          C * (1 + Real.log ((d : ℝ) * I.T)) ^ k *
            ((w : ℝ) * B + (d : ℝ) * I.T / Real.sqrt w) := by sorry

end DriftLinBandit.BOB
