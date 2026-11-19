-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
-- name    : EnvyFreeCake104.Divide.aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:55:48.605725+00:00
-- url     : https://prove2.me/theorems/191cd033-042f-4ee6-9757-2c28cee2f67e
-- title:
--   Sorted aligned cells determine prefix values and successor bounds
-- statement:
--   For any selected cell in the sorted cells of a valid aligned interval, its successor remains inside the interval. The preceding recorded sum bounds every prefix ending before the cell, and adding the value from the cell start gives every subsequent prefix value.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1

open EnvyFreeCake104.Divide
open scoped Classical

theorem EnvyFreeCake104.Divide.aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (I : Interval) (hI : 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts)
    (pre post : List ℝ) (c : ℝ)
    (hlist : ((s.pts.filter (fun d ↦ I.a ≤ d ∧ d < I.b)).sort (· ≤ ·)) =
      pre ++ c :: post) :
    c ∈ s.pts ∧ I.a ≤ c ∧ c < s.nextPt c ∧ s.nextPt c ≤ I.b ∧
      ∀ z : ℝ, z ∈ Set.Icc I.a I.b →
        (z ≤ c → (V i).value (Set.Ico I.a z) ≤ (pre.map (s.val i)).sum) ∧
        (c ≤ z → (V i).value (Set.Ico I.a z) =
          (pre.map (s.val i)).sum + (V i).value (Set.Ico c z)) := by sorry
