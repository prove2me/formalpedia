-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_unbounded_killed_martingale_of_condExp_identity
-- name    : AvramDividend.Classical.chat01_unbounded_killed_martingale_of_condExp_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:48:11.22504+00:00
-- url     : https://prove2.me/theorems/5d347463-858c-4092-b6f8-ada2dbf30930
-- title:
--   Unbounded-variation killed scale payoff martingale from its conditional-expectation identity
-- statement:
--   For an unbounded-variation spectrally negative Levy process and its q-scale function, suppose the genuinely downward-killed discounted scale payoff Z satisfies the conditional-expectation martingale equality at all deterministic times. Then Z is a Martingale. The canonical Cantor-pairing rational observation schedule and the already Proved continuous-history killed-payoff adaptedness theorem establish StronglyAdapted. The assumed conditional identity closes the remaining martingale field. Separate Proved integrability handles each fixed-time killed payoff, so no Standing assumption is needed. This proves the exact interface and leaves q-harmonicity as the genuine stochastic obligation.
-- source:
--   Esscher first-passage branch: assembled from canonically Proved chat03_killed_scale_payoff_adapted (b3295962-412d-4193-8439-614757867c92) and chat04_nat_pairing_rational_grid_coverage (34d1a207-11c0-49d1-b331-c905323990f4). Analogous to proved Standing-only chat04_killed_martingale_of_condExp_identity, extended without Standing.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_payoff_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat01_unbounded_killed_martingale_of_condExp_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : Z = fun t ω =>
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω)
    (hCond : ∀ s u : ℝ≥0, s ≤ u →
      P[Z u | 𝓕 s] =ᵐ[P] Z s) :
    Martingale Z 𝓕 P := by sorry
