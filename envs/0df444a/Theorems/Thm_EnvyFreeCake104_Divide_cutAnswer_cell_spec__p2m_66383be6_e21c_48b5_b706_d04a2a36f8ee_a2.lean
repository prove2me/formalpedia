-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- name    : EnvyFreeCake104.Divide.cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:01:31.677633+00:00
-- url     : https://prove2.me/theorems/4e5788f8-d027-4dae-a36f-d096d66feec1
-- title:
--   An integrable nonnegative density gives a least cut within a sufficiently valuable cell
-- statement:
--   For 0 ≤ a ≤ b ≤ 1 and 0 ≤ r ≤ Vᵢ([a,b)), cutAnswer belongs to [a,b], gives value r, and precedes every crossing in that interval. Zero requests and degenerate cells are included.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
    {ι : Type} (V : ι → Valuation) (i : ι) :
    ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z := by sorry
