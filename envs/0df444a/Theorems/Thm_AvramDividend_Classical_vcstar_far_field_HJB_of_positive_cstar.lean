-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_HJB_of_positive_cstar
-- name    : AvramDividend.Classical.vcstar_far_field_HJB_of_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T10:34:24.849091+00:00
-- url     : https://prove2.me/theorems/281b94c9-a665-4175-bd11-0e2934e68014
-- title:
--   Full dividend HJB identity at sufficiently large reserves above a positive canonical barrier
-- statement:
--   Given a q-scale function with positive canonical barrier and q>0, any real reserve x at least a+1+max(0,X.c/q) satisfies the actual HJB identity max(Γv−qv,1−v')=0 together with integrability in the Lévy generator domain. The substantive nonlocal jump-sign inequality, global monotonicity of vcstar, and eventual dominance of qv over the Lévy drift are proved as separate exact mathematical components. This result establishes the far-field HJB region without adding monotonicity or value-size assumptions to the conclusion, but does not assert the difficult near-barrier or boundary HJB inequalities.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_far_field_HJB_of_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
