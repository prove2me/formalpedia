-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- name    : EnvyFreeCake104.Divide.valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:50:48.039795+00:00
-- url     : https://prove2.me/theorems/34b14f73-cc4c-4f0d-ae29-5566441fcb8e
-- title:
--   Suffixes decrease as valid positions advance in list order
-- statement:
--   For any interval list and two valid positions, if the second position has a larger index, or the same index and a greater or equal coordinate, its suffix is contained in the first suffix. No well-formedness or spatial ordering assumption is needed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
    (Q : Piece) (p q : Pos) (hp : Q.ValidPos p) (hq : Q.ValidPos q)
    (hpq : p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) :
    (suffixList Q q).toSet ⊆ (suffixList Q p).toSet := by sorry
