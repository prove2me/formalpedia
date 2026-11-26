-- Prove2me | Theorems.Thm_Auto_exists_brascamp_lieb_memW0
-- name    : Auto.exists_brascamp_lieb_memW0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:55:46.935219+00:00
-- url     : https://prove2.me/theorems/d463a87d-895e-440e-9cb8-1f082795f57f
-- title:
--   Auto: exists brascamp lieb mem W0
-- statement:
--   **Proposition.**
--
--   Let  $m,l\in\mathbb{N}$, $m+l\le n$ and assume $l\neq 0$.
--   Let $J\in \mathbb{N}$ with $J\ge 1$. For $j\in [J)$, let $l_j\in \mathbb{N}$ and let
--   $\Pi_j:\mathbb{R}^m\times \mathbb{R}^l \to \mathbb{R}^{l_j}$
--   be a linear map such that
--
--   $$
--       \bigcap_{j\in [J)} {\rm ker}\Pi_j=\{0\}\, .
--   $$
--
--   Then there is $C>0$ such that the following holds.
--   For $j\in [J)$, let $f_j\in W_0(\mathbb{R}^{l_j})$. Then for each
--    $u\in \mathbb{R}^m$, the function
--
--   $$
--        v\to \prod_{j\in [J)}f_j(\Pi_{j}(u,v))
--   $$
--
--    is in $W_0(\mathbb{R}^l)$ and with $f$ defined by
--
--   $$
--           f(u)=\int_{\mathbb{R}^l}\prod_{j\in [J)}f_j(\Pi_{j}(u,v))\, dv \, ,
--   $$
--
--   we have $f\in W_0(\mathbb{R}^{m})$ and
--
--   $$
--           \|f\|_{W_0}\le C\prod_{j\in[J)}\|f_j\|_{W_0}\, .
--   $$
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2739-L2828
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2739-L2828

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.exists_brascamp_lieb_memW0
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {K : Type*} [NormedField K] [NormedSpace ℝ K]
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (π i).toLinearMap = ⊥) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → K,
      (∀ i, MemW0 (f i)) →
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) => ∏ i, f i (π i (u, v)))) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) =>
        ∫ v, ∏ i, f i (π i (u, v))) ∧
      (∫ u, wienerEnvelope
        (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, ∏ i, f i (π i (u, v))) 1 u) ≤
        C * ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by sorry
