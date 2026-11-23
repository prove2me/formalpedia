-- Prove2me | Theorems.Thm_Experiments_norm_replace_steps_le
-- name    : Experiments.norm_replace_steps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:48:53.690097+00:00
-- url     : https://prove2.me/theorems/b7b8cdee-3a22-4a63-bb38-77f11e73bfa5
-- title:
--   Experiments: norm replace steps le
-- statement:
--   Let `M` take `n` steps of size `h`, followed by `E` for a time `r`. Each step of `M` can be
--   replaced by a step of size `k` of `E` at the cost of `C D ‖M h - E k‖`, where `C` and `D` bound
--   `M` and `E` on `[0, t]`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L47-L77
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L47-L77

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]

theorem Experiments.norm_replace_steps_le (M E : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t) {t C D : ℝ}
    (hC : ∀ s ∈ Icc 0 t, ‖M s‖ ≤ C) (hD : ∀ s ∈ Icc 0 t, ‖E s‖ ≤ D) {h k : ℝ} (hh : 0 ≤ h)
    (hk : 0 ≤ k) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hnh : n * h ≤ t) (hnk : n * k + r ≤ t) :
    ‖M (n * h) * E r - E (n * k + r)‖ ≤ n * (C * D * ‖M h - E k‖) := by sorry
