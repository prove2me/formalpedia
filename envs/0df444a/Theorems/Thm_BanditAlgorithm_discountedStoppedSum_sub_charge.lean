-- Prove2me | Theorems.Thm_BanditAlgorithm_discountedStoppedSum_sub_charge
-- name    : BanditAlgorithm.discountedStoppedSum_sub_charge
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:45:31.534421+00:00
-- url     : https://prove2.me/theorems/f2334dc0-8a73-4a94-8e7b-36fa7a242be2
-- title:
--   Discounted stopping-block charge identity
-- statement:
--   For a trajectory whose discounted absolute rewards are summable, the net reward of a stopping block at constant charge $\gamma$ is
--
--   $$
--   \sum_{t<\tau}\alpha^t(r(S_t)-\gamma)
--   =
--   \sum_{t<\tau}\alpha^t r(S_t)
--   -\gamma\sum_{t<\tau}\alpha^t.
--   $$
--
--   The assumption $0\leq\alpha<1$ guarantees summability of the stopped discounted time series.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Eq. (35.7) on printed p.448 and Part 1 of the proof of Theorem 35.9 on printed p.452. This is the pathwise algebraic accounting identity for each prevailing-charge block.

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.discountedStoppedSum_sub_charge
    {S : Type*} {α γ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (r : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hsum : Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|)) :
    discountedStoppedSum α (fun y ↦ r y - γ) τ ω =
      discountedStoppedSum α r τ ω -
        γ * discountedStoppedSum α (fun _ : S ↦ 1) τ ω := by
  sorry
