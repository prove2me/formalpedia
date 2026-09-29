-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_lipschitz_charge
-- name    : BanditAlgorithm.gittinsRetirementValue_lipschitz_charge
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:54:16.403418+00:00
-- url     : https://prove2.me/theorems/598008c6-77f3-48ae-8ae1-324d879adbc8
-- title:
--   The Gittins retirement value is Lipschitz in the charge
-- statement:
--   Fix a state $x$ in a discounted one-armed retirement game satisfying the discounted absolute-reward integrability assumption. Let $v_{\gamma}(x)$ denote the optimal value when each played round incurs charge $\gamma$.
--
--   For any two charges $\gamma$ and $\delta$,
--
--   $$
--   \left|v_{\gamma}(x)-v_{\delta}(x)\right|
--   \le
--   |\gamma-\delta|\sum_{t=0}^{\infty}\alpha^t.
--   $$
--
--   Thus the retirement value is uniformly Lipschitz in the charge, with constant equal to the full discounted duration. This controls the boundary case where the charge approaches the fair Gittins index.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), printed p. 448, Eq. (35.7) and the observation immediately following Assumption 35.6 that the retirement value is decreasing in the charge; the quantitative bound follows directly from the discounted-duration bound used in printed p. 449, Lemma 35.7.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittinsRetirementValue_lipschitz_charge
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ δ : ℝ) :
    |gittinsRetirementValue P r α γ x -
        gittinsRetirementValue P r α δ x| ≤
      |γ - δ| * ∑' t : ℕ, α ^ t := by
  sorry
