-- Prove2me | Theorems.Thm_FD1D_dyadicTent_mul_eq_zero_of_separated
-- name    : FD1D.dyadicTent_mul_eq_zero_of_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:42.907396+00:00
-- url     : https://prove2.me/theorems/f29ead2e-7052-58e9-b3c0-f2d009b342ff
-- title:
--   FD1 D: dyadic Tent mul eq zero of separated
-- statement:
--   Tents with separated interiors have zero pointwise product.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L622-L636
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L622-L636

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.dyadicTent_mul_eq_zero_of_separated {l₁ p₁ l₂ p₂ z : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hsep : l₁ + p₁ ≤ l₂ ∨ l₂ + p₂ ≤ l₁) :
    dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z = 0 := by sorry
