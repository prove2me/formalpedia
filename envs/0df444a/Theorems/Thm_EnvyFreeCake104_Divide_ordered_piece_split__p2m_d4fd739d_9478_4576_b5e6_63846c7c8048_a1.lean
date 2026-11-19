-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- name    : EnvyFreeCake104.Divide.ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:40:18.288862+00:00
-- url     : https://prove2.me/theorems/4f88c27f-5aff-4766-80c5-ebd56db53b44
-- title:
--   Splitting ordered pieces preserves geometry and makes suffixes decrease with position
-- statement:
--   Splitting a well-formed ordered piece at a valid position produces well-formed complementary prefix and suffix pieces. The resulting suffix is a suffix by definition, and every later valid position produces a contained suffix. For the empty piece, any position is permitted.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
    (v : Valuation) (Q : Piece) (hQ : Q.WF) (p : Pos)
    (hp : Q = [] ∨ Q.ValidPos p) :
    (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
    v.value (suffixList Q p).toSet =
      v.value Q.toSet - v.value (prefixList Q p).toSet ∧
    IsSuffix (suffixList Q p).toSet Q ∧
    ∀ q : Pos, Q.ValidPos q →
      (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) →
      (suffixList Q q).toSet ⊆ (suffixList Q p).toSet := by sorry
