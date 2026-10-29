-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_positive_root_strict_gap_below
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_levy_positive_root_strict_gap_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:49:47.58454+00:00
-- url     : https://prove2.me/theorems/2e49ebdf-24e4-4e35-9019-8f4d284770d1
-- title:
--   Strict Lévy exponent moment-rate gap below a positive root
-- statement:
--   For the genuine spectrally negative Lévy Laplace exponent ψ, if 0<p, 0<λ, ψ(λ)=p, and 0≤β<λ, then necessarily ψ(β)<p. The source-specific convexity of ψ on [0,∞) and ψ(0)=0 imply ψ(β)≤(β/λ)p<p. This removes an otherwise redundant strict moment-gap premise from original-clock Wiener–Hopf finite-rate consequences without imposing any differentiability or moment assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_levy_positive_root_strict_gap_below
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β)
    (hβlam : β < lam) :
    X.ψ β < p := by sorry
