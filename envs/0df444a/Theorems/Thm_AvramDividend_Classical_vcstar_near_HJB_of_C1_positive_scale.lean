-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_C1_positive_scale
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_C1_positive_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:30:12.579898+00:00
-- url     : https://prove2.me/theorems/9ff66972-7c5f-44c6-93fe-1cd50aef4ad5
-- title:
--   Near-field HJB from positive C1 scale function without assuming canonical derivative minimality
-- statement:
--   Suppose the q-scale function W is continuously differentiable on strictly positive reserves and its ordinary derivative is everywhere strictly positive there, with q>0 and positive canonical real cstar. Then at every x>cstar with x≥1 and x≥cstar+max(0,X.c/q), the true spectrally negative Lévy generator of vcstar is integrable and the full HJB maximum equals zero. No separate assumption that cstar minimises W' is needed: pinned C1 regularity makes W' continuous, and the Proved cstar-toReal-zero-or-minimal theorem automatically gives derivative minimality when cstar is positive. The Proved near-HJB theorem then supplies the nonlocal generator and active HJB branch. This is still conditional on positive W' and C1 regularity, not a claim of unconditional optimality.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_C1_positive_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hderpos : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (hbarrier : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
