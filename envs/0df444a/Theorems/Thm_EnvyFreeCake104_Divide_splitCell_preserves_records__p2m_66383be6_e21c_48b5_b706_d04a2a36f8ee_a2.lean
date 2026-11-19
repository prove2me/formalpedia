-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- name    : EnvyFreeCake104.Divide.splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:01:39.051958+00:00
-- url     : https://prove2.me/theorems/1bf3b025-64da-41d3-a86c-e0243aee6483
-- title:
--   Splitting a recorded cell preserves all participating agents' records
-- statement:
--   Splitting strictly inside a recorded cell succeeds for every oracle and initial transcript, preserves valid records, and inserts exactly the splitting point.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) :
    ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts := by sorry
