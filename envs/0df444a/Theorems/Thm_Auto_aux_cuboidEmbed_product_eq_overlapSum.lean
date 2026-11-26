-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_product_eq_overlapSum
-- name    : Auto.aux_cuboidEmbed_product_eq_overlapSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:22.816318+00:00
-- url     : https://prove2.me/theorems/cf2a1b7a-3fc7-553d-a1bb-42c23bc1d389
-- title:
--   Auto: aux cuboid Embed product eq overlap Sum
-- statement:
--   On `[0,N)`, the cuboid product is a finite sum of the diagonal discrete
--   products over its common overlap intervals.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L975-L1042
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L975-L1042

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

theorem Auto.aux_cuboidEmbed_product_eq_overlapSum {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1)
    (hwidth : ε + δ < 1) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) N) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
      (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) =
      ∑ q : Fin N, aux_overlapContribution ε δ a k u q.val s := by sorry
