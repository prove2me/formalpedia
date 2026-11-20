-- Prove2me | Theorems.Thm_EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- name    : EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:35:34.739124+00:00
-- url     : https://prove2.me/theorems/f402ad90-5cdc-4dae-8aed-bffe50fa4e83
-- title:
--   Finite suffix enlargement and envy-cycle elimination reach a terminal allocation
-- statement:
--   Given finite suffix chains with nonnegative increments bounded by positive δ, obtain a δ-envy-free suffix allocation and paired agent/piece orders in which every non-whole bundle is strictly envied by an earlier agent. This is the source’s finite-state cycle-rotation and enlargement argument, followed by topological sorting. The remaining core work is formalizing its finite termination and invariant preservation; no greedy profiles enter this lemma.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (δ : ℝ) (hδ : 0 < δ) (m : ι → ℕ) (D : ι → ℕ → Set ℝ)
    (hD :
    ∀ j ∈ N,
      D j 0 = ∅ ∧ D j (m j) = (P j).toSet ∧
      (∀ k ≤ m j, IsSuffix (D j k) (P j)) ∧
      ∀ k < m j, D j k ⊆ D j (k + 1) ∧
        ∀ i ∈ N, 0 ≤ (V i).value (D j (k + 1)) - (V i).value (D j k) ∧
          (V i).value (D j (k + 1)) - (V i).value (D j k) ≤ δ) :
    ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
      (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
      (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ) ∧
    ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      g.1.zip g.2 = before ++ p :: after →
        X p.1 = (P p.2).toSet ∨
        ∃ q ∈ before, (V q.1).value (X q.1) < (V q.1).value (X p.1) := by sorry
