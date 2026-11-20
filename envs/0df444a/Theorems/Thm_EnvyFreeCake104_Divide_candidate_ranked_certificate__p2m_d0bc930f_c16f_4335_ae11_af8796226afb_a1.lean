-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- name    : EnvyFreeCake104.Divide.candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T07:02:56.075616+00:00
-- url     : https://prove2.me/theorems/5bed9376-8889-49fb-a2d7-44e0177be346
-- title:
--   Candidate geometry and a strictly descending indifference witness for every trimmed recipient
-- statement:
--   Every successful candidate has the exact residue and assigns suffixes according to a bijection. Each shortened recipient has an indifferent observer with strictly smaller natural-number rank. Envy-freeness of the candidate is not required.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (g : List ι × List ι) (hg : g ∈ guesses N) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (candidate N P g.1 g.2) s = some ((Y, R), s', tr)) :
    R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet ∧
    ∃ (π : ι → ι) (rank : ι → ℕ),
      Set.BijOn π (N : Set ι) (N : Set ι) ∧
      (∀ i ∈ N, IsSuffix (Y i).toSet (P (π i))) ∧
      ∀ i ∈ N, (Y i).toSet ≠ (P (π i)).toSet →
        ∃ j ∈ N, rank j < rank i ∧
          (V j).value (Y i).toSet = (V j).value (Y j).toSet := by sorry
