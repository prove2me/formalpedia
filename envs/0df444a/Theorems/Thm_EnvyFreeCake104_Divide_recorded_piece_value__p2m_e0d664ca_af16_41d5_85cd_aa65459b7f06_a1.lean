-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- name    : EnvyFreeCake104.Divide.recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:48:37.04776+00:00
-- url     : https://prove2.me/theorems/30dca544-0c8a-4339-b224-0ca0d046b555
-- title:
--   Recorded values equal true values on well-formed aligned pieces
-- statement:
--   For a participating agent, a valid record state computes the true value of every well-formed piece whose endpoints are recorded. Prove this by decomposing aligned intervals into recorded cells and applying finite additivity; endpoint singletons have zero integral.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
    {ι : Type} (V : ι → Valuation) (N : Finset ι) (s : Rec ι)
    (hs : s.Valid V N) (i : ι) (hi : i ∈ N) (P : Piece)
    (hP : P.WF) (hPs : s.Aligned P) :
    s.pieceVal i P = (V i).value P.toSet := by sorry
