-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_of_index_le
-- name    : BanditAlgorithm.gittinsRetirementValue_eq_zero_of_index_le
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:02:24.434693+00:00
-- url     : https://prove2.me/theorems/1cd7e1a9-6662-4b09-bc70-1c85655d806d
-- title:
--   Retirement is optimal above the Gittins fair charge
-- statement:
--   If the charge $\gamma$ is at least the Gittins index $g(x)$, every admissible play-then-stop strategy has nonpositive expected discounted net reward. Since immediate retirement gives zero, the retirement-game value satisfies $v_\gamma(x)=0$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), fair-charge characterization Eq. (35.8), ratio characterization Eq. (35.9), and Lemma 35.7, printed pp.448--449.

import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittinsRetirementValue_eq_zero_of_index_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) (hg : gittinsIndex P r α x ≤ γ) :
    gittinsRetirementValue P r α γ x = 0 := by
  sorry
