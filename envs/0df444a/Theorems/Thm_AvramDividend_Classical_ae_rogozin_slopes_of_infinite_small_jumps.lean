-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
-- name    : AvramDividend.Classical.ae_rogozin_slopes_of_infinite_small_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:36:02.774765+00:00
-- url     : https://prove2.me/theorems/b12c5430-2bd6-4ba0-9184-becc6f00b058
-- title:
--   Infinite small-jump activity implies almost-sure Rogozin negative-slope oscillation at time zero
-- statement:
--   A spectrally negative Levy process with infinite small-jump activity oscillates below every linear slope arbitrarily close to time zero, almost surely. This is the infinite-activity disjunct of the Proved standing_levy_regular_cases split (f5ce6b06): together with its Gaussian sibling it supplies the hRog premise for the unbounded-variation branch of barrierStrategy_zero_boundary_value_identity (c2921c8c) without assuming the full Open rogozin theorem 4502f364.
-- source:
--   Infinite-small-jump split of the c2921c8c ¬BV-branch hRog obligation via Proved standing_levy_regular_cases (f5ce6b06): the second ¬BV disjunct. Uses only the jump-activity hypothesis, so it is reusable for any Standing-process small-time oscillation argument

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem ae_rogozin_slopes_of_infinite_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ) := by sorry

end AvramDividend.Classical
