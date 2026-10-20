-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_field_jump_nonpos_of_affine_majorant
-- name    : AvramDividend.Classical.vcstar_near_field_jump_nonpos_of_affine_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:52:32.316695+00:00
-- url     : https://prove2.me/theorems/f7e6fed9-23c2-45eb-9696-e6688abb08ff
-- title:
--   Near-field nonlocal generator inequality from the affine majorant above reserve one
-- statement:
--   Let x exceed the canonical real dividend barrier a and also satisfy x≥1. Assume the candidate barrier value is globally monotone and lies below its affine extrapolation from the cap on 0≤z≤a. Then compensated negative jumps y∈(-1,0) remain at nonnegative reserves; those staying above a cancel exactly while those crossing below a have nonpositive compensated increment by the affine-majorant hypothesis. For y≤−1 monotonicity makes the uncompensated increment nonpositive. Consequently the entire nonlocal jump integral is nonpositive, and if q*vcstar W x≥X.c, the Lévy generator residual is nonpositive with actual generator integrability. This covers reserves potentially strictly closer to a than the earlier a+1 far-field condition. The affine-majorant hypothesis remains a genuine independent shape obligation.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_field_jump_nonpos_of_affine_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hmono : Monotone (vcstar W))
    (hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal)
    (x : ℝ)
    (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by sorry
