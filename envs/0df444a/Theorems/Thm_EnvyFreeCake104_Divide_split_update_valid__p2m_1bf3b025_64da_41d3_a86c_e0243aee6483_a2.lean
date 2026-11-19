-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- name    : EnvyFreeCake104.Divide.split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:49:41.349181+00:00
-- url     : https://prove2.me/theorems/a7ea23eb-ef9f-4670-a599-a32a93d4b6dc
-- title:
--   The explicit interior-cell update preserves valid records
-- statement:
--   The explicit update preserves validity when c is recorded and c < y < nextPt c. Establish the successor changes using finite-set minima, then use integral additivity on the two half-open subcells. This isolates the geometric and valuation argument from program execution. Empty participation, zero densities, and a successor equal to one are allowed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (c y : ℝ)
    (hc : c ∈ s.pts) (hcy : c < y) (hyn : y < s.nextPt c) :
    ({
             pts := insert y s.pts
             val := fun i x ↦
               if i ∈ N then
                 if x = c then evalAnswer V i c y
                 else if x = y then s.val i c - evalAnswer V i c y
                 else s.val i x
               else s.val i x
             prefixCuts := s.prefixCuts } : Rec ι).Valid V N := by sorry
