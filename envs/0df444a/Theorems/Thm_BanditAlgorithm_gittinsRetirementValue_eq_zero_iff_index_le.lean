-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_iff_index_le
-- name    : BanditAlgorithm.gittinsRetirementValue_eq_zero_iff_index_le
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:09:14.205039+00:00
-- url     : https://prove2.me/theorems/c7fbf6a5-73c3-41db-868b-1d5ae9e269a6
-- title:
--   Gittins index as the fair retirement charge
-- statement:
--   The retirement-game value at state $x$ is zero exactly when the charge is at least the Gittins index:
--
--   $$v_\gamma(x)=0\quad\Longleftrightarrow\quad g(x)\leq\gamma.$$
--
--   Thus the stopping-ratio definition of $g(x)$ agrees with its fair-charge characterization.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Eqs. (35.8)--(35.9), printed pp.448--449.

import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_of_index_le
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_pos_of_lt_index

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittinsRetirementValue_eq_zero_iff_index_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) :
    gittinsRetirementValue P r α γ x = 0 ↔
      gittinsIndex P r α x ≤ γ := by
  sorry
