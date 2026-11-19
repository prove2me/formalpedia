-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- name    : EnvyFreeCake104.Divide.splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:49:36.342262+00:00
-- url     : https://prove2.me/theorems/7063f87d-5f7a-4f69-9dda-6499da5371ba
-- title:
--   Cell splitting executes the explicit simultaneous record update
-- statement:
--   Cell splitting succeeds with the explicit simultaneous update for arbitrary records, endpoints, oracle, and transcript. Induct over the duplicate-free participant list, preserving unvisited rows and threading the transcript. This isolates operational semantics from validity. Empty participation and coincident endpoints are allowed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (c y : ℝ) (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ tr : List (Event ι),
      Prog.run V o ((splitCell N c y).run s) tr₀ =
        some (((), ({
             pts := insert y s.pts
             val := fun i x ↦
               if i ∈ N then
                 if x = c then evalAnswer V i c y
                 else if x = y then s.val i c - evalAnswer V i c y
                 else s.val i x
               else s.val i x
             prefixCuts := s.prefixCuts } : Rec ι)), tr) := by sorry
