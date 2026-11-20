-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- name    : EnvyFreeCake104.Divide.trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:12:33.611502+00:00
-- url     : https://prove2.me/theorems/e3d0eb38-1d43-46ed-9031-5ca1f6a426ac
-- title:
--   A changed trimmed piece has an indifferent reference agent
-- statement:
--   For any successful trimming run with valid records and well-formed aligned bundles, a change in the input piece’s underlying set yields a reference agent indifferent between the final piece and that agent’s fixed bundle. The removed-piece accumulator is arbitrary.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF)
    (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
    (Q removed : Piece) (hQ : Q.WF) (s : Rec ι) (hs : s.Valid V N)
    (hYs : ∀ i ∈ N, s.Aligned (Y i)) (hQs : s.Aligned Q)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (B rem : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((trimAgainst N Y earlier Q removed).run s) tr₀ =
      some (((B, rem), s'), tr))
    (hchanged : B.toSet ≠ Q.toSet) :
    ∃ j ∈ earlier, (V j).value B.toSet = (V j).value (Y j).toSet := by sorry
