-- Prove2me | Theorems.Thm_Auto_fintype_tensor_wienerNorm_le
-- name    : Auto.fintype_tensor_wienerNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:08.282885+00:00
-- url     : https://prove2.me/theorems/f075b1ad-a6a6-5318-86f5-e9926551a4c7
-- title:
--   Auto: fintype tensor wiener Norm le
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
--   See also `Auto.MemW0.fintype_tensor`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2613-L2631
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2613-L2631

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.fintype_tensor_wienerNorm_le {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i)) :
    (∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)),
      wienerEnvelope (fun y : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (y i)) 1 x) ≤
      ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by sorry
