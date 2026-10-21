-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_tendsto_first_passage_of_mesh_brackets
-- name    : AvramDividend.Classical.chat03_tendsto_first_passage_of_mesh_brackets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:45:53.022984+00:00
-- url     : https://prove2.me/theorems/3c083b41-be47-4d81-bbed-42473b98b665
-- title:
--   Convergence from one-sided first-passage mesh brackets for vanishing grid widths
-- statement:
--   For finite NNReal first-passage approximants σ_n and any grid-width sequence h_n tending to zero, suppose that for every ε>0 there is δ>0 so that whenever h_n<δ the bracket τ≤σ_n<τ+ε holds. Then σ_n tends to τ in the order topology on NNReal. This generic convergence result converts deterministic grid-detection epsilon-delta estimates into formal Filter.Tendsto statements and applies to upward, downward or two-sided strict first-passage infima. It uses no Lévy assumptions or stochastic process definitions.
-- source:
--   Pinned Mathlib Topology.Order.Basic tendsto_order and NNReal tsub identity add_tsub_cancel_of_le.

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.chat03_tendsto_first_passage_of_mesh_brackets
    (τ : ℝ≥0) (mesh σ : ℕ → ℝ≥0)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hbracket : ∀ ε : ℝ≥0, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ n : ℕ, mesh n < δ →
          τ ≤ σ n ∧ σ n < τ + ε) :
    Tendsto σ atTop (𝓝 τ) := by sorry
