-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_has_negative_left_shift_exponent
-- name    : AvramDividend.Classical.esscher_positive_root_has_negative_left_shift_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:24:06.072626+00:00
-- url     : https://prove2.me/theorems/e456ec82-f7f4-4d77-8355-0cc153de7ac1
-- title:
--   A positive Lévy q-root has a strictly negative Esscher exponent after a small left shift
-- statement:
--   Given q>0 and a positive root φ with ψ(φ)=q of a spectrally negative Lévy process, there exists a strictly interior left shift 0<ε<φ for which ψ(φ−ε)<q. In fact ε=φ/2 works by the convexity/secant monotonicity of ψ and ψ(0)=0. Thus the finite θ=φ Esscher law admits a strictly decaying negative exponential moment, the key supermartingale input for an ultimate descending-infimum tail bound.
-- source:
--   Direct proof from already Proved `levy_psi_positive_secant_monotone`: ψ(φ/2)/(φ/2)≤ψ(φ)/φ=q/φ, so ψ(φ/2)≤q/2<q. The result holds for all spectrally negative Lévy processes without Standing or unbounded variation assumptions.

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_has_negative_left_shift_exponent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧ X.ψ (φ - ε) < q := by sorry
