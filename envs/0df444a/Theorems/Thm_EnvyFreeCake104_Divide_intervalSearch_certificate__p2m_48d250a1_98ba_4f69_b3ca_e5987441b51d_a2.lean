-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- name    : EnvyFreeCake104.Divide.intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:46:46.750743+00:00
-- url     : https://prove2.me/theorems/518aa50c-865e-406f-a8d5-8825bd8e452f
-- title:
--   Interval search returns a residual with strict bounds on skipped prefixes
-- statement:
--   For a nonempty interval list and a nonnegative request bounded by its recorded total, interval search succeeds. Its residual is nonnegative, fits the selected interval, and balances the completed value; every skipped interval ends strictly below the request.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
    {ι : Type} (s : Rec ι) (i : ι) (Q : Piece) (hne : Q ≠ [])
    (w : ℝ) (hw : 0 ≤ w) (hbudget : w ≤ s.pieceVal i Q) :
    ∃ (k : ℕ) (r : ℝ),
      findInterval s i Q 0 w = some (k, r) ∧
      k < Q.length ∧ 0 ≤ r ∧ r ≤ s.intervalVal i (Q.getD k default) ∧
      s.pieceVal i (Q.take k) + r = w ∧
      ∀ j : ℕ, j < k → s.pieceVal i (Q.take (j + 1)) < w := by sorry
