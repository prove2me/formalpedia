-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- name    : EnvyFreeCake104.Divide.alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:47:00.0162+00:00
-- url     : https://prove2.me/theorems/ee4ea07c-74b1-4666-9e33-804cbad52afb
-- title:
--   Sorted cell search and least cuts give the first crossing within an aligned interval
-- statement:
--   For a participating agent in a valid record, cell search on a well-formed interval with recorded endpoints succeeds for every admissible residual. Under the supplied least-cut contract, the returned endpoint has exactly the requested prefix value and is the earliest crossing.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (I : Interval) (hI : 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts)
    (r : ℝ) (hr : 0 ≤ r) (hrI : r ≤ s.intervalVal i I) :
    ∃ x : ℝ,
      (if r ≤ 0 then some I.a else
        match findCell s i
            ((s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)) r with
        | none => none
        | some (c, t) => some (cutAnswer V i c t)) = some x ∧
      I.a ≤ x ∧ x ≤ I.b ∧ (V i).value (Set.Ico I.a x) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc I.a I.b →
        r ≤ (V i).value (Set.Ico I.a z) → x ≤ z := by sorry
