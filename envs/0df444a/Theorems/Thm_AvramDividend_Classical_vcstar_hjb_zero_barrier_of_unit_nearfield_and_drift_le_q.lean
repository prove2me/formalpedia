-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_zero_barrier_of_unit_nearfield_and_drift_le_q
-- name    : AvramDividend.Classical.vcstar_hjb_zero_barrier_of_unit_nearfield_and_drift_le_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:26:48.719719+00:00
-- url     : https://prove2.me/theorems/d9027af3-1858-40b3-8e03-3faf666dcf97
-- title:
--   Zero-barrier HJB reduces to the unit near-field when Lévy drift does not exceed discount
-- statement:
--   Under cstar=0 and the quantitative drift condition X.c≤q, the HJB equality at every positive reserve follows from integrability and nonpositivity of the generator residual only for reserves strictly between zero and one. For reserves at least one, the discount term already dominates the drift; the verified far-field HJB lemma applies. Below one, the zero-barrier derivative is exactly one and the given residual bound closes the maximum equation. This isolates the remaining jump-integrability work to a bounded interval adjacent to zero.
-- source:
--   Proved far-field HJB equality c757837b-a9a1-4f02-aea0-f3dfa3eb79c9 and affine derivative 4098a584-9c09-4437-b71f-5590221db9ab.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_hjb_zero_barrier_of_unit_nearfield_and_drift_le_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (hcost : X.c ≤ q)
    (hsmall : ∀ y : ℝ, 0 < y → y < 1 →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
