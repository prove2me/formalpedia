-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- name    : EnvyFreeCake104.Divide.prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:40:06.431787+00:00
-- url     : https://prove2.me/theorems/66383be6-e21c-48b5-b706-d04a2a36f8ee
-- title:
--   Prefix-cut execution preserves records and returns the first value crossing
-- statement:
--   Under the parent's exact hypotheses, prefixCut succeeds, preserves valid records and existing points, produces aligned pieces, and returns a prefix of value w whose position precedes every valid position with prefix value at least w. The empty-piece case is explicitly permitted.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (i : ι) (hi : i ∈ N) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (p : Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (Q = [] ∨ Q.ValidPos p) ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      ∀ q : Pos, Q.ValidPos q → w ≤ (V i).value (prefixList Q q).toSet →
        p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2) := by sorry
