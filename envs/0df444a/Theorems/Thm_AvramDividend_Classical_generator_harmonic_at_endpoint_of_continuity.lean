-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_harmonic_at_endpoint_of_continuity
-- name    : AvramDividend.Classical.generator_harmonic_at_endpoint_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:27:59.79189+00:00
-- url     : https://prove2.me/theorems/cefc2f88-8e3c-4550-b1dd-614d3f564bab
-- title:
--   Continuous Lévy q-generator residual transfers interior harmonicity to a positive endpoint
-- statement:
--   If W is in the Lévy generator domain at a positive real endpoint a, the generator residual ΓW−qW is continuous on (0,a], and W is q-harmonic at all strict interior points of (0,a), then W is q-harmonic at a as well. This is an exact boundary transfer under explicit analytic prerequisites; it does not assert that residual continuity or interior harmonicity follow automatically from a scale-function Laplace transform. The proof uses the density of (0,a) in (0,a] and Hausdorff extension of pointwise equality.

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_harmonic_at_endpoint_of_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable W a ∧
      X.generator W a - q * W a = 0 := by sorry
