-- Prove2me | Theorems.Thm_EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- name    : EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:18:49.748608+00:00
-- url     : https://prove2.me/theorems/9307d7ac-a474-42b4-b7f1-6bf0b2d91a86
-- title:
--   Greedy suffix profiles admit arbitrarily envy-free extensions
-- statement:
--   This is the finite-cell construction in the supplied source’s proof of Lemma 6. For positive δ, subdivide each ordered piece into finitely many consecutive cells worth at most δ to every participating agent, using integrability without normalization. Start with labeled empty suffixes, rotate strict envy cycles, and otherwise enlarge an unenvied non-whole suffix by its preceding cell. Enlargements are finite; between enlargements rotations strictly increase own-value sum among finitely many assignments. The process preserves δ-envy-freeness. At termination, topological ordering and suffix comparability show that the corresponding greedy profile is contained in the terminal allocation. This removes the discrete approximation argument from the parent. Empty and zero-valued pieces cause no obstruction; no claim is made for δ ≤ 0.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (C : (List ι × List ι) → ι → Set ℝ)
    (hC : ∀ g ∈ guesses N, EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g)) :
    ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
        (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
        (∀ i ∈ N, C g i ⊆ X i) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ) := by sorry
