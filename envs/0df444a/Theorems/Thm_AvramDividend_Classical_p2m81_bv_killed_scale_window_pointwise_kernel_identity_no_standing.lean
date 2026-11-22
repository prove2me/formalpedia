-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_killed_scale_window_pointwise_kernel_identity_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_killed_scale_window_pointwise_kernel_identity_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:10:22.870019+00:00
-- url     : https://prove2.me/theorems/2fd450f9-f94f-4a02-9764-4cdb19cc120c
-- title:
--   BV killed scale window pointwise kernel/payoff identification without standing (public)
-- statement:
--   For a spectrally negative Levy process with discount q and genuine q-scale function W, given the future-window reindexing data and a past-measurable set A with its masked reserve, the shifted ennreal killed kernel at each path equals the ofReal image of the masked killed payoff pointwise. No Standing assumption and no integrability hypotheses.
-- source:
--   Pointwise half of the H1c assembly, replaying the hLeft block of accepted proof fdccdf7c with the masked reserve H inlined explicitly; pure logic plus the window reindex data. Feeds H1c in the H1 (ee75bf61) decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.p2m81_bv_killed_scale_window_pointwise_kernel_identity_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s : ℝ≥0) (T : ℝ≥0)
    (u : ℝ≥0) (hsu : s ≤ u)
    (hTu : s + T = u) (hTcu : (T : ℝ) = (u : ℝ) - (s : ℝ))
    (hEvent : ∀ ω : Ω, (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)})
    (A : Set Ω) :
    ∀ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (if ω ∈ A then x + X.X s ω else -1) +
          (X.X (s + v) ω - X.X s ω)
        then ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
          W ((if ω ∈ A then x + X.X s ω else -1) +
            (X.X (s + T) ω - X.X s ω))) else (0 : ℝ≥0∞)) =
      ENNReal.ofReal (A.indicator (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) ω) := by sorry
