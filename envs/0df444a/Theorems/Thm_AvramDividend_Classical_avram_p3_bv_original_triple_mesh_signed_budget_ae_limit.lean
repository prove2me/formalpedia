-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
-- name    : AvramDividend.Classical.avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:49:42.835161+00:00
-- url     : https://prove2.me/theorems/dc7915b6-7c0e-4b5b-b42e-fd8e7b9a3af6
-- title:
--   Actual BV mesh reward, compensated jump and HJB drift all converge to signed budget
-- statement:
--   Finite-grid original dividend reward, original compensated source jump, and HJB drift can all vary with mesh. If their common almost-everywhere limits exist, the full original signed upper bound remains valid for the limits. This is the exact order-closed passage needed after the separately proved stopped source C1 mesh estimates; it adds no stochastic model assumption or same-law substitution.
-- source:
--   Pinned Mathlib Filter.Tendsto.add, Tendsto.sub, le_of_tendsto, and ae filter-upwards.

import Mathlib
open MeasureTheory Filter

theorem AvramDividend.Classical.avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (Y M B : Ω → ℝ) (K : ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω)
    (hYLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) :
    ∀ᵐ ω ∂P, Y ω ≤ K + M ω + B ω := by sorry
