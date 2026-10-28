-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_distinct_of_joint_product_atomless
-- name    : AvramDividend.Classical.ae_distinct_of_joint_product_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:06:05.110061+00:00
-- url     : https://prove2.me/theorems/e64d957a-0ab9-4e20-aa96-d98a7a18cd21
-- title:
--   Independent real arrival-time variables with diffuse second marginal almost surely do not coincide
-- statement:
--   Let U,V be real-valued measurable random variables on an arbitrary sample space, whose joint pushforward law equals a product of measures μ×ν. If the second marginal ν is s-finite and atomless, then U and V are almost surely unequal. Proof: the diagonal has zero product measure by ae_prod_iff_ae_ae and NullSingletonClass, then use the measurable-pushforward ae_map_iff. This is a precise probability-level precursor for obtaining pairwise no-simultaneous-time events in a canonical Poisson point family whenever two distinct marks have independent diffuse time marginals.
-- source:
--   Pinned Mathlib MeasureTheory.ae_prod_iff_ae_ae, Measure.ae_ne, ae_map_iff. Unlike the stronger desired Poisson result, pairwise product-law independence is explicitly hypothesised.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_distinct_of_joint_product_atomless
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Ω → ℝ)
    (hUV : Measurable (fun ω => (U ω, V ω)))
    (μ ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (hjoint : P.map (fun ω => (U ω, V ω)) = μ.prod ν) :
    ∀ᵐ ω ∂P, U ω ≠ V ω := by sorry
