-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
-- name    : AvramDividend.Classical.avram_p4_f6_renewal_cdf_atomless_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:21:46.889659+00:00
-- url     : https://prove2.me/theorems/109f9c15-0c2c-464f-8039-67a33134e1b1
-- title:
--   Atomless locally finite renewal-measure CDF is continuous on the positive half-line
-- statement:
--   The cumulative renewal measure ν((0,x]) has no jumps at positive x when every singleton has zero ν-mass. Local finiteness and continuity from above/below give continuous real-valued CDF on [0,∞). This is a deterministic measure-continuity component of the Gaussian zero-scale existence construction.
-- source:
--   Continuity of atomless measure distributions under local finiteness; measure continuity from above and below, with zero singleton masses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_renewal_cdf_atomless_continuous
    (ν : Measure ℝ)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) :
    ContinuousOn (fun x : ℝ => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) (Ici (0 : ℝ)) := by sorry
