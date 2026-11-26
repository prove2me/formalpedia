-- Prove2me | Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap
-- name    : Auto.MemW0.aux_comp_injective_continuousLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:29.269494+00:00
-- url     : https://prove2.me/theorems/16dfb71f-a174-5d72-aeb5-302703036526
-- title:
--   Mem W0: aux comp injective continuous Linear Map
-- statement:
--   Pullback along an injective linear map between finite-dimensional Euclidean spaces preserves
--   `W₀`.  The proof identifies the range with a coordinate factor through an orthogonal
--   decomposition, restricts to that factor, and then changes coordinates on the domain.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1679-L1720
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1679-L1720

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_comp_injective_continuousLinearMap {k n : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin n) → 𝕜} (hf : MemW0 f)
    (π : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    MemW0 (f ∘ π) := by sorry
