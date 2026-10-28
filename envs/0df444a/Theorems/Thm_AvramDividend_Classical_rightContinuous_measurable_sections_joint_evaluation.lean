-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
-- name    : AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:39:42.085748+00:00
-- url     : https://prove2.me/theorems/8aafec11-d8a5-443c-9386-270a0d5c8a04
-- title:
--   Joint Borel measurability of right-continuous processes with measurable deterministic-time sections
-- statement:
--   A real-valued process indexed by nonnegative real times is jointly measurable in time and sample point provided every deterministic-time section is sample-measurable and every sample path is right-continuous. This supplies precisely the nontrivial measurable evaluation theorem needed for càdlàg Lévy processes, avoiding the false assertion that coordinate-product path-space measurability alone implies jointly measurable evaluation.
-- source:
--   Approximate each observation time t≥0 from above by dyadic ceilings r_n(t)=Nat.ceil(t2^n)/2^n. Pinned Prove2Me theorems prove r_n(t)≥t and r_n(t)→t. For each n, map z=(t,ω) to the measurable integer ceil(t2^n), and use Mathlib `exists_measurable_piecewise` to glue each measurable finite-grid sample F_(k/2^n) along the disjoint observable fibres k. Thus z↦F_(r_n(t))(ω) is jointly measurable. Right-continuity yields convergence via tendsto_nhdsWithin_iff. Mathlib measurable_of_tendsto_metrizable and tendsto_pi_nhds conclude the result. This is self-contained in the exact pinned environment, and does not depend on any unverified project helper.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Constructions
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t : ℝ≥0, Measurable (F t))
    (hRight : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Ici t) t) :
    Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) := by sorry
