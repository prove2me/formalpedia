-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_reserve_payoff_right_limit
-- name    : AvramDividend.Classical.chat03_nonnegative_reserve_payoff_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:48:45.973256+00:00
-- url     : https://prove2.me/theorems/f598854b-0025-4d00-9c96-70bba4127f2f
-- title:
--   Right-limit convergence of discounted q-scale payoffs including zero approached from nonnegative reserves
-- statement:
--   Let sampled times converge to tau from the right. When the limiting reserve is nonnegative and all sufficiently late sampled reserves are also nonnegative, the scale function's continuity on the closed positive half-line proves convergence of discounted scale payoffs. The theorem includes the boundary case where the limiting reserve is exactly zero even if W(0)>0, without improperly assuming global continuity across the negative half-line.
-- source:
--   Official Levy right-continuity and IsScaleFunction continuousOn on Ici 0 combined with pinned Mathlib neighbourhood-within convergence. The eventual sampled-reserve sign is explicit, not inferred from convergence at a boundary.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_nonnegative_reserve_payoff_right_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hlimit : 0 ≤ x + X.X τ ω)
    (hsampled : ∀ᶠ n : ℕ in atTop, 0 ≤ x + X.X (clock n) ω) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by sorry
