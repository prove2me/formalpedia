-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- name    : EnvyFreeCake104.Divide.disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:09:41.354666+00:00
-- url     : https://prove2.me/theorems/cd65bf21-858b-401d-ae0a-ebc005f0a031
-- title:
--   Valuation is additive over a well-formed list of intervals
-- statement:
--   The valuation of a well-formed piece equals the list sum of the valuations of its pairwise disjoint intervals.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
    (v : Valuation) (P : Piece) (hP : P.WF) :
    (P.map (fun I ↦ v.value I.toSet)).sum = v.value P.toSet := by sorry
