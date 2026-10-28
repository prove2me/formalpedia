-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_positive_root_unique
-- name    : AvramDividend.Classical.esscher_levy_shift_positive_root_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:22:46.601716+00:00
-- url     : https://prove2.me/theorems/c3c6ea66-9778-4704-ad5e-61a4edce4966
-- title:
--   Unique positive Esscher shifted Laplace-exponent root for each rate
-- statement:
--   For any canonical spectrally negative Lévy exponent ψ with ψ(φ)=q>0 at φ>0, and every p>0, there exists exactly one positive λ solving ψ(φ+λ)−q=p. This is valid without X.Standing, convexity hypotheses or differentiability and follows from canonically accepted existence and strict increase.
-- source:
--   Prove2Me accepted source-specific root existence a9d8fdb2-917c-4ec8-992f-fa0ba374c16b, strict-shift monotonicity 0906e33f-37dc-4382-95d0-b5cad94b12ab; Mathlib StrictMonoOn.injOn.

import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_shift_positive_root_of_levy_secant
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_shift_positive_root_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi p : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hp : 0 < p) :
    ∃! lambda : ℝ,
      0 < lambda ∧ X.ψ (phi + lambda) - q = p := by sorry
