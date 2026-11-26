-- Prove2me | Theorems.Thm_Auto_MemW0_fintype_tensor
-- name    : Auto.MemW0.fintype_tensor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:49.086468+00:00
-- url     : https://prove2.me/theorems/82c7b46a-568d-4354-a4d2-3b0b398aa533
-- title:
--   Mem W0: fintype tensor
-- statement:
--   **Proposition.**
--
--   Let $J\in \mathbb{N}$ with $J\ge 1$. For $j\in [J)$, let $I_j\subset \mathbb{N}$ and assume the
--   $I_j$ are pairwise disjoint.
--   Set $I=\bigcup_{j\in [J)}I_j$. Let $f_j:\mathbb{R}^{|I_j|}\to \mathbb{K}$ in $W_0(|I_j|)$ and define
--
--   $$
--           f(x_I)=\prod_{j\in [J)}f_j(x_{I_j})\, .
--   $$
--
--   Then $f\in W_0(|I|)$ and
--
--   $$
--           \|f\|_{W_0}\le \prod_{j\in [J)}\|f_j\|_{W_0}\, .
--   $$
--
--   See also `Auto.fintype_tensor_wienerNorm_le`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2577-L2592
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2577-L2592

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.fintype_tensor {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i)) :
    MemW0 (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) := by sorry
