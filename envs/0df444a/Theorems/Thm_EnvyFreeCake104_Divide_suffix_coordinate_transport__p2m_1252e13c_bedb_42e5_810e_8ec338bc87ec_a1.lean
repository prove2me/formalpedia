-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
-- name    : EnvyFreeCake104.Divide.suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:06:38.065363+00:00
-- url     : https://prove2.me/theorems/cb2654a9-6e4a-4858-adf0-f02709568413
-- title:
--   Valid positions and repeated cuts under suffix coordinates
-- statement:
--   After a valid cut at p, a position q in the retained list is valid exactly when its index translated by p's index is valid in the original list, with the additional lower-endpoint constraint at local index zero. Cutting again at q gives exactly the original list cut at that translated position.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
    (Q : Piece) (p : Pos) (hp : Q.ValidPos p) (q : Pos) :
    ((suffixList Q p).ValidPos q ↔
      Q.ValidPos (p.1 + q.1, q.2) ∧ (q.1 = 0 → p.2 ≤ q.2)) ∧
    ((suffixList Q p).ValidPos q →
      suffixList (suffixList Q p) q = suffixList Q (p.1 + q.1, q.2)) := by sorry
