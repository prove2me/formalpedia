-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- name    : EnvyFreeCake104.Divide.cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:09:36.632028+00:00
-- url     : https://prove2.me/theorems/5a00f621-960f-4528-b9d5-a60d4ec27d12
-- title:
--   Recorded successor cells partition an interval for valuation integration
-- statement:
--   For an interval with ordered endpoints in a finite record set contained in the cake, the sum of its successor-cell values equals its interval value, including the convention at endpoint 1.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
    {ι : Type} (v : Valuation) (s : Rec ι) (I : Interval)
    (hpts : ∀ c ∈ s.pts, 0 ≤ c ∧ c ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts) (hab : I.a ≤ I.b) :
    (∑ c ∈ s.pts.filter (fun c ↦ I.a ≤ c ∧ c < I.b),
      v.value (Set.Ico c (s.nextPt c))) = v.value I.toSet := by sorry
