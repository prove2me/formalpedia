-- Prove2me | Theorems.Thm_EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- name    : EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:19:08.109834+00:00
-- url     : https://prove2.me/theorems/bf3c702a-024b-4f33-8628-cda081118fd2
-- title:
--   Compactness upgrades approximate extensions to an envy-free greedy profile
-- statement:
--   This isolates the source’s final compactness argument for an arbitrary family of greedy profiles. First prove the pure greedy analogue of Claim 7 by induction over positions. Hence a failed profile has no envy-free suffix extension. Parametrize extensions by total suffix length in each ordered piece; these parameters form a nonempty compact box, including singleton factors for empty pieces. Integrability gives continuous valuation functions, and the finite maximum envy attains a strictly positive minimum for every failed profile. Take the minimum over finitely many guesses and apply happrox below that positive threshold. Mathlib’s IsCompact.exists_isMinOn supports the extreme-value step. The core obligation is the suffix parametrization and continuity proof; strict positivity is inferred only under failure, so zero valuations and plateaus are preserved.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (C : (List ι × List ι) → ι → Set ℝ)
    (hC : ∀ g ∈ guesses N, EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g))
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
        (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
        (∀ i ∈ N, C g i ⊆ X i) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ)) :
    ∃ g ∈ guesses N, EnvyFree V N (C g) := by sorry
