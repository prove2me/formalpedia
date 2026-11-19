-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- name    : EnvyFreeCake104.Divide.cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:50:45.355201+00:00
-- url     : https://prove2.me/theorems/2412efb0-419b-4f88-9b27-9423e1e4ae36
-- title:
--   A valid cut partitions a well-formed ordered piece into well-formed disjoint parts
-- statement:
--   Cutting a well-formed ordered piece at a valid position yields well-formed prefix and suffix pieces whose underlying sets are disjoint and have union equal to the original piece. Cuts at either endpoint and degenerate intervals are included.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
    (Q : Piece) (hQ : Q.WF) (p : Pos) (hp : Q.ValidPos p) :
    (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
    Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
    (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by sorry
