-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_renewal_kernel_contractivity_of_standing
-- name    : AvramDividend.Classical.bv_renewal_kernel_contractivity_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:03:01.581225+00:00
-- url     : https://prove2.me/theorems/fa89f310-81b5-497a-bdb5-2881eebe5d10
-- title:
--   Contractive positive renewal discount from bounded-variation Lévy standing assumptions
-- statement:
--   The canonical Standing and BoundedVariation hypotheses imply positive drift and finite truncated magnitude moment. The previously accepted contractive-kernel theorem then guarantees an integer discount with strictly sub-drift renewal mass. This provides a direct stochastic-to-analytic adapter for the bounded-variation construction.
-- source:
--   Canonical Classical SpectrallyNegativeLevy 933ced80; Proved c04fb14e and 35bb663a; pinned Mathlib 0df444a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_positive_jump_moment_finite
import Theorems.Thm_AvramDividend_Classical_discounted_renewal_kernel_mass_small
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_renewal_kernel_contractivity_of_standing {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      ENNReal.ofReal (q / ((n : ℝ) + 1)) +
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1))
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
        ENNReal.ofReal X.drift := by
  sorry
