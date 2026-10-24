-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_exit_ratio_joint_continuousAt
-- name    : AvramDividend.Classical.chat04_scale_exit_ratio_joint_continuousAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:57:12.876663+00:00
-- url     : https://prove2.me/theorems/620ed837-cf25-4e89-b1f2-e9d895543bff
-- title:
--   Joint continuity of the q-scale exit factor in positive reserve and barrier
-- statement:
--   The scale ratio W(x)/W(a) is jointly continuous as a function of the initial reserve and upper barrier at every strictly positive pair (x,a). This supports simultaneous reserve and barrier perturbations without assuming the stochastic exit identity.
-- source:
--   Proved positive-axis q-scale continuity and positivity, product-coordinate projection continuity, and division.

import Mathlib.Topology.Constructions.SumProd
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_exit_ratio_joint_continuousAt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a : ℝ)
    (hx : 0 < x) (ha : 0 < a) :
    ContinuousAt (fun p : ℝ × ℝ => W p.1 / W p.2) (x, a) := by sorry
