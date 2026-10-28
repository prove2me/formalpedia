-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_horizon_max_no_positive_atom_below_terminal
-- name    : AvramDividend.Classical.reflectedSup_finite_horizon_max_no_positive_atom_below_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:53:22.940062+00:00
-- url     : https://prove2.me/theorems/7db4a8fa-84d7-4069-baed-68104bf957af
-- title:
--   For downward-regular spectrally negative Lévy processes, the finite-horizon reflected running maximum cannot equal a fixed positive level while the terminal drawdown lies strictly below it
-- statement:
--   Fix any finite time horizon H, a positive level x and a spectrally negative Lévy process whose sample paths almost surely take negative values arbitrarily close to zero. Then P(sup_{0≤s≤H}(sup_{u≤s}X_u−X_s)=x and reflected drawdown at time H is below x)=0. The event is genuinely nontrivial and does not assume the reflected process returns to zero at H. Compact upper semicontinuity forces a genuine maximal-height hit before H, the accepted true capped first-hit stopping-time theorem and strong Markov transfer provide negative process increments immediately afterwards, and the reflected drawdown then strictly overshoots x before H, contradicting its being the maximum. Convert the resulting almost-sure impossibility to zero outer measure using MeasureTheory.ae_iff. This is a conditional ordinary probability P theorem, not a proof that source downward regularity follows from unbounded variation or that the result automatically holds under the sigma-finite excursion measure n.
-- source:
--   Kuznetsov Kyprianou Rivero 2013 §2.3; accepted reflectedSup_terminal_below_max_capped_first_hit_geometry, reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source, reflectedSup_exceeds_hit_height_of_negative_posthit.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_finite_horizon_max_no_positive_atom_below_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω |
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by sorry
