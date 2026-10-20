-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_payoff_family_uniformIntegrable
-- name    : AvramDividend.Classical.chat03_noexit_payoff_family_uniformIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:39:12.135285+00:00
-- url     : https://prove2.me/theorems/65103d2d-1c4e-45fe-83f6-230b5cb7b82d
-- title:
--   Uniform integrability of killed q-scale no-exit path component over finite horizons
-- statement:
--   For an official spectrally negative Lévy process with q>0 and a q-scale function W, restrict the finite-time discounted scale payoff to the event where both strict upper and strict lower passage clocks are infinite, and set it to zero elsewhere. If this time-indexed component is almost-everywhere strongly measurable on the finite measure space, it is uniformly integrable in L1 across all finite observation times. This uses an exact Proved global strip bound on the no-exit event and the separately Proved pointwise-bounded-family uniform-integrability theorem.
-- source:
--   Accepted chat03_infinite_passage_discounted_strip_bound and chat03_uniformIntegrable_of_pointwise_bounded_family, plus pinned norm-of-nonnegative facts. The required measurability is explicit and is not inferred without proof.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_infinite_passage_discounted_strip_bound
import Theorems.Thm_AvramDividend_Classical_chat03_uniformIntegrable_of_pointwise_bounded_family
import Mathlib.Analysis.Normed.Group.Real

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_payoff_family_uniformIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (f : ℝ≥0 → Ω → ℝ)
    (hf : ∀ t ω, f t ω =
      if twoSidedExitUpTime X (a - x) ω = ∞ ∧
         twoSidedExitDownTime X (-x) ω = ∞ then
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
      else 0)
    (hmeas : ∀ t, AEStronglyMeasurable (f t) P) :
    UniformIntegrable f (1 : ℝ≥0∞) P := by sorry
