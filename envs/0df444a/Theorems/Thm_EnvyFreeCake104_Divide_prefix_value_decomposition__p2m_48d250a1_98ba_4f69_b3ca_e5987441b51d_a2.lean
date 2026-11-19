-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- name    : EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:46:53.803611+00:00
-- url     : https://prove2.me/theorems/c352c62d-d5ac-4bcc-999b-94964f7c4827
-- title:
--   A valid prefix has completed recorded value plus its partial interval value
-- statement:
--   For a well-formed aligned piece with correct recorded values, a valid prefix has value equal to its completed recorded value plus its partial interval value, and is bounded by the completed value through its current interval.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
    {ι : Type} (V : ι → Valuation) (s : Rec ι) (i : ι)
    (hrecord : ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet)
    (Q : Piece) (hQ : Q.WF) (hQs : s.Aligned Q)
    (p : Pos) (hp : Q.ValidPos p) :
    (V i).value (prefixList Q p).toSet =
        s.pieceVal i (Q.take p.1) +
          (V i).value (Set.Ico (Q.getD p.1 default).a p.2) ∧
      (V i).value (prefixList Q p).toSet ≤
        s.pieceVal i (Q.take (p.1 + 1)) := by sorry
