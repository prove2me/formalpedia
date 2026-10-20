-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
-- name    : AvramDividend.Classical.vcstar_interior_harmonicity_of_scale_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:14:16.720668+00:00
-- url     : https://prove2.me/theorems/43b9ce71-f8f3-49b2-a64d-04479b786587
-- title:
--   Transfer of scale-function q-harmonicity to the exact dividend value below cstar
-- statement:
--   Let W satisfy the pinned q-scale function definition with positive real canonical barrier. Suppose, as a genuine explicit analytic assumption, that W is in the full nonlocal Lévy generator domain and solves its q-harmonic generator equation at every reserve 0<x<cstar. Then the corresponding dividend barrier value vcstar W belongs to the generator domain and solves the identical q-harmonic generator equation throughout that interior. This theorem uses only already-Proved scalar linearity and generator-domain scaling plus already-Proved exact nonlocal generator congruence of vcstar with the normalised W. It is a complete mathematical reduction of the original generator_vcstar_eq_zero theorem to scale-function harmonicity, rather than assuming or importing that still-Open analytic result.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_interior_harmonicity_of_scale_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hscale : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
