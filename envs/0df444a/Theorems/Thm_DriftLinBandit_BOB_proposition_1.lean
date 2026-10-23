-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_proposition_1
-- name    : DriftLinBandit.BOB.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:56.105028+00:00
-- url     : https://prove2.me/theorems/df314125-354f-4d25-8e20-c4dcdc9aa1d8
-- title:
--   Proposition 1, p. 15 — R_T(BOB) = Õ(w†B_T + dT/√w† + Q√(|J|T/H))
-- statement:
--   Fix positive constants $R,L,S,\lambda$ with $\lambda S^2\ge1$. There are constants $C>0$ and $k\in\mathbb N$, depending only on $R,L,S,\lambda$, such that for every dimension $d\ge1$, every drifting linear bandit instance with horizon $T\ge1$ satisfying the standing assumptions and Assumption 1, every $B_T\ge0$ with $\sum_{t=1}^{T-1}\|\theta_{t+1}-\theta_t\|_2\le B_T$, and every i.i.d. centred $R$-sub-Gaussian noise, the regret of BOB with the parameters $H,\Delta,J,Q,\gamma$ of (11)–(12) is integrable and, for every window $w^\dagger\in J$,
--   $$
--   \mathcal R_T(\text{BOB})\le C\,(1+\ln(dT))^k\Big(w^\dagger B_T+\frac{dT}{\sqrt{w^\dagger}}+Q\sqrt{\frac{|J|\,T}{H}}\Big).
--   $$
--   In particular the bound holds at the best window of $J$, the paper's $w^\dagger$: $\mathcal R_T(\text{BOB})=\widetilde O(w^\dagger B_T+dT/\sqrt{w^\dagger}+Q\sqrt{|J|T/H})$.
--
--   The first two terms are SW-UCB's regret with the best window in $J$; the third is EXP3's cost of learning that window. Theorem 4 follows by inserting the parameters (11).
--
--   **Formalization Note.** $\widetilde O$ as in Theorem 3, with $C,k$ fixed before $d,T,B_T$, the instance and the noise. $|J|$ is $\Delta+1$. The regret of BOB averages over EXP3's draws through the finite mixture of the `Bob` definitions. SW-UCB inside BOB uses $\lambda$ and $\delta=1/T$ (Appendix C). No restriction $H\le T$ is imposed.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 15, Proposition 1 (15); Appendix E, pp. 39–40

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model
import Definitions.Def_DriftLinBandit_BOB_Bob

namespace DriftLinBandit.BOB

open MeasureTheory

/-- Proposition 1 (p. 15): the dynamic regret of BOB is `Õ(w†B_T + dT/√w† + Q√(|J|T/H))`, where
`w†` is the best window size in `J`. For all positive `R, L, S, λ` with `λS² ≥ 1` there are
constants `C > 0` and `k` (depending only on `R, L, S, λ`) such that for every dimension `d ≥ 1`,
every instance with horizon `T ≥ 1` satisfying the standing assumptions and Assumption 1, every
`B ≥ 0` with `∑_{t=1}^{T−1} ‖θ_{t+1} − θ_t‖₂ ≤ B` and every i.i.d. centred `R`-sub-Gaussian noise,
BOB with the parameters (11)–(12) has integrable regret and, for every candidate window
`w = ⌊H^{j/Δ}⌋ ∈ J`, `R_T(BOB) ≤ C (1 + ln(dT))^k (w B + dT/√w + Q √((Δ+1)T/H))`. -/
theorem proposition_1 (R L S lam : ℝ) (hR : 0 < R) (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam)
    (hlamS : 1 ≤ lam * S ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (d : ℕ), 1 ≤ d → ∀ (I : Instance d), 1 ≤ I.T → I.Standing L S → Assumption1 I →
      ∀ (B : ℝ), 0 ≤ B → variation I ≤ B →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), IsSubGNoise P η R →
        Integrable (bobRegretMix I R L S lam η) P ∧
        ∀ j : Fin (bobDelta d I.T + 1),
          ∫ ω, bobRegretMix I R L S lam η ω ∂P ≤
            C * (1 + Real.log ((d : ℝ) * I.T)) ^ k *
              ((bobJ d I.T j : ℝ) * B + (d : ℝ) * I.T / Real.sqrt (bobJ d I.T j) +
                bobQ R d I.T *
                  Real.sqrt (((bobDelta d I.T : ℝ) + 1) * I.T / (bobH d I.T : ℝ))) := by sorry

end DriftLinBandit.BOB
