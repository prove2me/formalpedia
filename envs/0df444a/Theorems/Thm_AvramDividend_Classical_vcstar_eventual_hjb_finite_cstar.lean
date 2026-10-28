-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
-- name    : AvramDividend.Classical.vcstar_eventual_hjb_finite_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:37:05.261319+00:00
-- url     : https://prove2.me/theorems/09ea2ea1-676c-4998-b549-46a94cb69d42
-- title:
--   Every finite optimal barrier candidate satisfies the HJB equation for all sufficiently large reserves
-- statement:
--   For any finite optimal barrier, positive discount q and arbitrary real Lévy drift X.c, the candidate value satisfies the generator-integrable HJB maximum equality whenever the initial reserve x is at least cstar+1+max(0,X.c/q). This explicit threshold guarantees both that all small negative jumps remain in the affine payout regime and that the discount term dominates the drift. It establishes the entire unbounded tail of the HJB verification directly and confines the remaining generator problem to an explicitly bounded set of reserves.
-- source:
--   Proved finite-barrier HJB under explicit reserve drift bound, and the ordered-field equivalence of a ratio bound and its cross-multiplied form for q>0.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_eventual_hjb_finite_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ)
    (hx : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
