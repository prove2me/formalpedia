-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- name    : EnvyFreeCake104.Divide.permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T06:47:06.879651+00:00
-- url     : https://prove2.me/theorems/fe6a13c9-fa8f-488c-9456-5b7086e2c57f
-- title:
--   Permute uses at most n+1 queries per counted prefix cut
-- statement:
--   Every successful Permute execution makes at most n+1 Robertson–Webb queries per increment of the prefix-cut counter, without validity, positivity, or well-formedness assumptions.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (s : Rec ι) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (permute N P) s = some ((Y, R), s', tr)) :
    queryCount tr ≤ (N.card + 1) * (s'.prefixCuts - s.prefixCuts) := by sorry
