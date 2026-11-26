-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_integrand_toLp
-- name    : Auto.aux_cuboidEmbed_integrand_toLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:29.777168+00:00
-- url     : https://prove2.me/theorems/1e268e53-83e2-585b-989a-3cc3774f1343
-- title:
--   Auto: aux cuboid Embed integrand to Lp
-- statement:
--   The cuboid lifts have the expected integrand after passing from raw
--   coordinates to `ctRealVector n`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L639-L648
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L639-L648

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

theorem Auto.aux_cuboidEmbed_integrand_toLp {n : ℕ} {ε δ : ℝ}
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (s : ℝ) :
    (∏ i, aux_liftRaw (aux_cuboidEmbed ε δ i (a i))
        (WithLp.toLp 2 (fun j ↦ (k j : ℝ) + u j) + s • ctCoordinateAxis i)) =
      ∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) := by sorry
