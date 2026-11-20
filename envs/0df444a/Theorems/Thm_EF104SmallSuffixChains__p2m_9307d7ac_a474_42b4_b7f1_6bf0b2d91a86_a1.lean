-- Prove2me | Theorems.Thm_EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- name    : EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:35:32.546464+00:00
-- url     : https://prove2.me/theorems/99142f0d-48c1-4bba-8593-cef73a2796b8
-- title:
--   Finite suffix chains with uniformly small valuation increments
-- statement:
--   For every positive δ, each participating well-formed ordered piece admits a finite nested chain of suffixes from empty to whole, with each successive increment worth at most δ to every participating agent. Prove this using absolute continuity of the finitely many integrable densities and a common fine subdivision. No normalization is needed, and empty pieces may use a zero-length chain.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ι → ℕ) (D : ι → ℕ → Set ℝ),
    ∀ j ∈ N,
      D j 0 = ∅ ∧ D j (m j) = (P j).toSet ∧
      (∀ k ≤ m j, IsSuffix (D j k) (P j)) ∧
      ∀ k < m j, D j k ⊆ D j (k + 1) ∧
        ∀ i ∈ N, 0 ≤ (V i).value (D j (k + 1)) - (V i).value (D j k) ∧
          (V i).value (D j (k + 1)) - (V i).value (D j k) ≤ δ := by sorry
