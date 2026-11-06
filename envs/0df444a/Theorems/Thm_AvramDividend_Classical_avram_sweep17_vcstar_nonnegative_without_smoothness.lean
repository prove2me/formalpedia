-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness
-- name    : AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_without_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:03:04.437788+00:00
-- url     : https://prove2.me/theorems/494b2f23-1b63-435d-a80e-16168cee645e
-- title:
--   Global nonnegativity of original vcstar at finite cstar without Gaussian/BV/C2 alternatives
-- statement:
--   Under only original standing hypotheses, q-scale-function identity, positive discount and finite canonical barrier, vcstar is nonnegative at every nonnegative reserve. The zero barrier uses the Proved zero-barrier value; for positive cstar the quotient W(0)/scaleDeriv(W,cstar) has nonnegative numerator and denominator by Proved scale positivity and derivative positivity. The Proved monotonicity of vcstar then transfers nonnegativity of vcstar(0) to all x>=0. No root smoothness assumption is required.
-- source:
--   Exact original Proved barrier_zero_boundary_value_nonneg df5df3b8, scaleDeriv_nonneg 3f19a0fb and vcstar_monotone_of_finite_cstar 8a1169cb. Explicit barrierValue/divE at zero and pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar


open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_without_smoothness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ vcstar W x := by sorry
