-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- name    : EnvyFreeCake104.Divide.candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:12:29.66635+00:00
-- url     : https://prove2.me/theorems/2a34ca2a-650a-4889-96ad-7ccf35f2b7ad
-- title:
--   Candidate removed prefixes are exactly the unallocated cake
-- statement:
--   Every successful candidate run on disjoint well-formed aligned input pieces returns exactly the unallocated portion of their union as its residue. No envy-freeness or nonemptiness hypothesis is required.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (g : List ι × List ι) (hg : g ∈ guesses N) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (candidate N P g.1 g.2) s = some ((Y, R), s', tr)) :
    R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet := by sorry
