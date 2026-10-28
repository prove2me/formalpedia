-- Prove2me | Theorems.Thm_AvramDividend_Classical_stronglyProgressive_of_past_finiteRange_sample
-- name    : AvramDividend.Classical.stronglyProgressive_of_past_finiteRange_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:27:32.878677+00:00
-- url     : https://prove2.me/theorems/7df3b423-32b1-4b19-8dc8-9af4109bf68d
-- title:
--   Finite-range past-time sampling of an adapted process is progressive
-- statement:
--   Let D be a strongly adapted real process. Suppose g(t) is a measurable sampling time no later than t, with only finitely many values on each bounded interval [0,T]. Then D(g(t)) is progressively measurable. At a fixed horizon T, partition time by the finitely many values of g; each cell is Borel and each fixed-time random variable D(s) is measurable for the terminal filtration F_T because s≤T. This is the missing measurable-step lemma for floor-grid approximations of left-continuous admissible dividend controls.
-- source:
--   Finite-horizon adapted sampling by measurable finite-range past-time selectors, elementary product-measurability argument. Connects the pinned Mathlib progressive-process definitions to the stochastic verification proof programme.

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stronglyProgressive_of_past_finiteRange_sample
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (g : ℝ≥0 → ℝ≥0) (hg_meas : Measurable g)
    (hg_past : ∀ t, g t ≤ t)
    (hg_finite : ∀ T, (g '' Iic T).Finite) :
    IsStronglyProgressive 𝓕 (fun t ω => D (g t) ω) := by sorry
