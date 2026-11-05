-- Prove2me | Theorems.Thm_FloorRecurrence_finite_base_all_width
-- name    : FloorRecurrence.finite_base_all_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/c5abc2d6-7202-4346-839a-0ab55f4a6d51
-- title:
--   FloorRecurrence: Finite base all width
-- statement:
--   No base-growth hypothesis is needed: a fixed finite base is absorbed by the explicit boundConstant. The sole cost premise is the physical recurrence.
--
--   Polynomial bounds for floor recurrences under explicit contraction, overhead, and finite base-case hypotheses. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L115-L127). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L115-L127 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators

theorem FloorRecurrence.finite_base_all_width {ι : Type} (rows : List ι) (c : ι → ℝ) (t : ι → ℕ)
    (m : ℕ) (f : ℕ → ℝ) (p C γ : ℝ)
    (hm : 0 < m) (hp : 0 ≤ p)
    (hc : ∀ i ∈ rows, 0 ≤ c i) (ht : ∀ i ∈ rows, 0 < t i)
    (htm : ∀ i ∈ rows, t i < m)
    (hγ : γ = (rows.map (fun i => c i * ((t i : ℝ) / m) ^ p)).sum) (hγ1 : γ < 1)
    (physical_recurrence : ∀ e, m ≤ e →
      f e ≤ C + (rows.map (fun i => c i * f (t i * (e / m)))).sum) :
    ∀ e, 0 < e → f e ≤ boundConstant m f C γ * (e : ℝ) ^ p := by sorry
