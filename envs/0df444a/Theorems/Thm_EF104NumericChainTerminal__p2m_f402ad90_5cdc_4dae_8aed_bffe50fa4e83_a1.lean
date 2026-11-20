-- Prove2me | Theorems.Thm_EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- name    : EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:03:08.422407+00:00
-- url     : https://prove2.me/theorems/d6700b1f-143c-4d41-968d-f3d8228d6a26
-- title:
--   Finite numerical chains admit an acyclic terminal approximate envy-free state
-- statement:
--   Zero-start finite numerical chains with nonnegative increments bounded by positive δ admit a permuted δ-envy-free state with acyclic strict envy, in which every unenvied agent receives a final chain entry.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

theorem EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
    {ι : Type} [DecidableEq ι] (N : Finset ι) (hN : N.Nonempty)
    (m : ι → ℕ) (u : ι → ι → ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ i ∈ N, ∀ j ∈ N, u i j 0 = 0)
    (hstep : ∀ j ∈ N, ∀ k < m j, ∀ i ∈ N,
      0 ≤ u i j (k + 1) - u i j k ∧ u i j (k + 1) - u i j k ≤ δ) :
    ∃ σ : Equiv.Perm ι, (∀ i, i ∈ N ↔ σ i ∈ N) ∧
      ∃ k : ι → ℕ,
        (∀ i ∈ N, k i ≤ m (σ i)) ∧
        (∀ i ∈ N, ∀ j ∈ N,
          u i (σ j) (k j) ≤ u i (σ i) (k i) + δ) ∧
        (∀ i, ¬ Relation.TransGen
          (fun a b ↦ a ∈ N ∧ b ∈ N ∧ u a (σ a) (k a) < u a (σ b) (k b)) i i) ∧
        ∀ j ∈ N, k j = m (σ j) ∨
          ∃ i ∈ N, u i (σ i) (k i) < u i (σ j) (k j) := by sorry
