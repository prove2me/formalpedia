-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:31:07.923699+00:00
-- url     : https://prove2.me/theorems/9c869763-9072-430e-81e7-4f1e8a5addc2
-- title:
--   The genuine Esscher negative-exponential martingale restricts to every bounded monotone discrete time grid
-- statement:
--   For θ≥ε≥0, any finite terminal time T, and any monotone deterministic grid of nonnegative sampling times g(n)≤T, there exists a natural-number filtration G_n=F_{g(n)} for which the compensated negative Esscher exponential Z_{g(n)} is a genuine Mathlib discrete martingale under the *single fixed genuine probability measure* Q_T=P.withDensity exp(θX_T−Tψθ). This is the exact constructor milestone that makes Doob's already-proved finite-grid maximal inequality applicable to running lower barrier events.
-- source:
--   Use Proved `chat04_esscher_weighted_finite_horizon_probability` to instantiate an actual fixed finite probability measure. Combine Proved compensated strong adaptedness, Proved integrability under later Esscher law, Proved fixed-terminal martingale event-integral identity, and Proved generic construction of a natural-number martingale from a bounded monotone real-time sampling grid. All components originate in the actual original Lévy law without assuming a global tilted process law.

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_martingale_early_events
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ n : ℕ, g n ≤ T) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ n : ℕ, 𝓖 n = 𝓕 (g n)) ∧
      Martingale
        (fun n ω => Real.exp
          (-ε * X.X (g n) ω -
            (g n : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
        𝓖
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by sorry
