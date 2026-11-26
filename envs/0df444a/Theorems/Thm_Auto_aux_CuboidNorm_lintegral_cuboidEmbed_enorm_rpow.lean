-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_cuboidEmbed_enorm_rpow
-- name    : Auto.aux_CuboidNorm.lintegral_cuboidEmbed_enorm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:49.746153+00:00
-- url     : https://prove2.me/theorems/b92eded3-40f4-5242-b6e3-ce621a1f240a
-- title:
--   aux Cuboid Norm: lintegral cuboid Embed enorm rpow
-- statement:
--   The finite-support `L^q` integral formula for the cuboid lift.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1534-L1554
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1534-L1554

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.lintegral_cuboidEmbed_enorm_rpow {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ y, ‖aux_cuboidEmbed ε δ i a y‖ₑ ^ q ∂volume) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q *
        ∏ j, ENNReal.ofReal (if j = i then δ else ε) := by sorry
