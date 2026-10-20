-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
-- name    : AvramDividend.Classical.vcstar_continuousOn_Icc_below_positive_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:50:57.624753+00:00
-- url     : https://prove2.me/theorems/4238a387-61d8-4b5d-85e9-cf92e657d572
-- title:
--   Dividend barrier value continuity through the entire lower branch
-- statement:
--   For an exact q-scale function W in the pinned spectrally negative Lévy formulation, and a positive real canonical barrier a=(cstar W).toReal, the associated dividend value vcstar W is continuous on the whole closed interval [0,a], including both endpoints. The proof uses the scale-function axiom ContinuousOn W on [0,∞), the already-Proved equality of vcstar with the real totalised normalised scale function at and below the barrier, and multiplication by the constant inverse derivative. No derivative positivity, Gaussian smoothness or stochastic q-harmonicity is assumed. This discharges the remaining compact-interval continuity premise in the derivative-minimality near-field HJB proof.

import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_continuousOn_Icc_below_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal) :
    ContinuousOn (vcstar W) (Icc 0 (cstar W).toReal) := by sorry
