-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_theorem_4
-- name    : DriftLinBandit.BOB.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:02.620763+00:00
-- url     : https://prove2.me/theorems/897941ce-74f0-4f1d-be67-1d495a41151b
-- title:
--   Theorem 4, p. 16 — BOB has dynamic regret Õ(d^{2/3}B_T^{1/3}T^{2/3} + d^{1/2}T^{3/4}) without knowing B_T
-- statement:
--   Fix positive constants $R,L,S,\lambda$ with $\lambda S^2\ge1$. There are constants $C>0$ and $k\in\mathbb N$, depending only on $R,L,S,\lambda$, such that the following holds. For every dimension $d\ge1$, every drifting linear bandit instance with horizon $T\ge1$ satisfying the standing assumptions ($\|X\|_2\le L$, $|\langle X,\theta_t\rangle|\le1$, $\|\theta_t\|_2\le S$, nonempty finite $D_t$) and Assumption 1, every variation budget $B_T\ge0$ with
--   $$
--   \sum_{t=1}^{T-1}\|\theta_{t+1}-\theta_t\|_2\le B_T ,
--   $$
--   and every i.i.d. centred $R$-sub-Gaussian noise, the Bandit-over-Bandit algorithm with the parameters (11)–(12) has integrable regret and
--   $$
--   \mathcal R_T(\text{BOB})\le C\,(1+\ln(dT))^k\big(d^{2/3}B_T^{1/3}T^{2/3}+d^{1/2}T^{3/4}\big),
--   $$
--   that is, $\mathcal R_T(\text{BOB})=\widetilde O(d^{2/3}B_T^{1/3}T^{2/3}+d^{1/2}T^{3/4})$.
--
--   BOB does not use $B_T$. When $B_T\ge d^{-1/2}T^{1/4}$ the bound matches, up to logarithmic factors, the rate $d^{2/3}B_T^{1/3}T^{2/3}$ that SW-UCB attains only when tuned with knowledge of $B_T$.
--
--   **Formalization Note.** $\widetilde O$ is read as the existence of $C,k$ chosen before $d$, $T$, $B_T$, the instance and the noise, with logarithmic factor $(1+\ln(dT))^k$. SW-UCB inside BOB uses $\lambda$ with $\lambda S^2\ge1$ and $\delta=1/T$ (the paper's Appendix C choices). $B_T$ is any upper bound on the variation (the paper's regime $B_T=\Theta(T^\rho)$ is not imposed). Argmax ties are broken by a fixed enumeration of $D_t$, and EXP3's randomisation enters as a finite mixture over choice sequences. Integrability is asserted, so that the bound is not satisfied by the default value of a non-integrable integral.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 16, Theorem 4; parameters (11)–(12), pp. 14–15; Appendix F, p. 41

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model
import Definitions.Def_DriftLinBandit_BOB_Bob

namespace DriftLinBandit.BOB

open MeasureTheory

/-- Theorem 4 (p. 16): with the parameters (11)–(12), the dynamic regret of BOB is
`Õ(d^{2/3} B_T^{1/3} T^{2/3} + d^{1/2} T^{3/4})`, without BOB knowing `B_T`. For all positive
`R, L, S, λ` with `λS² ≥ 1` there are constants `C > 0` and `k` (depending only on `R, L, S, λ`)
such that for every dimension `d ≥ 1`, every instance with horizon `T ≥ 1` satisfying the standing
assumptions and Assumption 1, every `B ≥ 0` with `∑_{t=1}^{T−1} ‖θ_{t+1} − θ_t‖₂ ≤ B` and every
i.i.d. centred `R`-sub-Gaussian noise, the regret of BOB is integrable and
`R_T(BOB) ≤ C (1 + ln(dT))^k (d^{2/3} B^{1/3} T^{2/3} + d^{1/2} T^{3/4})`. -/
theorem theorem_4 (R L S lam : ℝ) (hR : 0 < R) (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam)
    (hlamS : 1 ≤ lam * S ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (d : ℕ), 1 ≤ d → ∀ (I : Instance d), 1 ≤ I.T → I.Standing L S → Assumption1 I →
      ∀ (B : ℝ), 0 ≤ B → variation I ≤ B →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), IsSubGNoise P η R →
        Integrable (bobRegretMix I R L S lam η) P ∧
        ∫ ω, bobRegretMix I R L S lam η ω ∂P ≤
          C * (1 + Real.log ((d : ℝ) * I.T)) ^ k *
            ((d : ℝ) ^ ((2 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) * (I.T : ℝ) ^ ((2 : ℝ) / 3) +
              (d : ℝ) ^ ((1 : ℝ) / 2) * (I.T : ℝ) ^ ((3 : ℝ) / 4)) := by sorry

end DriftLinBandit.BOB
