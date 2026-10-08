-- Prove2me | Theorems.Thm_FlowJobShop_SPT_sorted_prefix_le
-- name    : FlowJobShop.SPT.sorted_prefix_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:16:39.143001+00:00
-- url     : https://prove2.me/theorems/57f30502-cedb-4edf-90cb-b8e99e00f290
-- title:
--   Proof of Lemma 9 — sorted prefix sums are smallest, $\sum_{j\le k}L_{i_j}\ge\sum_{j\le k}L_j$
-- statement:
--   Let $L_0,\dots,L_{n-1}$ be real numbers and let $\sigma$ be a bijection of $\{0,\dots,n-1\}$ that lists them in nondecreasing order, $L_{\sigma(0)}\le L_{\sigma(1)}\le\cdots\le L_{\sigma(n-1)}$. Then for every bijection $\rho$ of $\{0,\dots,n-1\}$ and every $k$,
--   $$
--   \sum_{j=0}^{k} L_{\sigma(j)}\ \le\ \sum_{j=0}^{k} L_{\rho(j)} .
--   $$
--   The sum of any $k+1$ of the numbers is at least the sum of the $k+1$ smallest. In the proof of Lemma 9 (with the jobs renumbered so that $L_1\le\cdots\le L_n$) this is the step $\sum_{j=1}^k L_{i_j}/m\ge\sum_{j=1}^k L_j/m$.
--
--   **Formalization Note** Positions are 0-based; the statement is purely combinatorial and is not tied to a scheduling instance.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 47, §2, proof of Lemma 9 ('Σ_{j=1}^k L_{i_j}/m ≥ Σ_{j=1}^k L_j/m')

import Mathlib

namespace FlowJobShop.SPT

/-- Prefix sums are smallest in sorted order: if `σ` lists `Fin n` so that `L (σ 0) ≤ L (σ 1) ≤ ⋯`,
then for every bijection `ρ` and every `k`, `∑_{j ≤ k} L_{σ j} ≤ ∑_{j ≤ k} L_{ρ j}`
(Gonzalez–Sahni 1978, proof of Lemma 9, p. 47: `∑_{j=1}^k L_{i_j}/m ≥ ∑_{j=1}^k L_j/m`). -/
theorem sorted_prefix_le {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by sorry

end FlowJobShop.SPT
