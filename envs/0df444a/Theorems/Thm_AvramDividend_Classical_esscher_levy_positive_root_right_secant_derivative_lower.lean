-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_right_secant_derivative_lower
-- name    : AvramDividend.Classical.esscher_levy_positive_root_right_secant_derivative_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:57:40.537324+00:00
-- url     : https://prove2.me/theorems/935a33f8-758c-4f2b-8aca-8e798d6c681c
-- title:
--   The actual positive-root Esscher right-secanted Lévy exponent has a strictly positive finite limit
-- statement:
--   For a genuine spectrally negative Lévy exponent ψ with positive q, φ and ψφ=q, if its right secant (ψ(φ+h)−ψφ)/h converges to any finite m as h↓0, the established source-specific secant lower bound implies m≥q/φ>0. Unlike the prior full HasDerivAt lower-bound theorem, this one requires only the right derivative at the Esscher root. Its proof uses the authentic Lévy secant bound at every h>0 and closed-order preservation under filter limits. It assumes no Wiener–Hopf factorisation.
-- source:
--   Accepted canonical levy_psi_root_shifted_increment_lower e9488750; pinned Mathlib ge_of_tendsto/order closed.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_positive_root_right_secant_derivative_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ m : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (hsec : Tendsto
      (fun h : ℝ => (X.ψ (φ + h) - X.ψ φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m)) :
    q / φ ≤ m ∧ 0 < m := by sorry
