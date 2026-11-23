-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Thick_mul_abs_sub_lt
-- name    : Formalism.BehrendSets.Thick.mul_abs_sub_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:14.8058+00:00
-- url     : https://prove2.me/theorems/91cf778f-ef47-4e3d-8be8-3fdbea507985
-- title:
--   Thick: mul abs sub lt
-- statement:
--   The Thick construction uses the mul abs sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/MulAbsSubLt.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/MulAbsSubLt.lean#L12-L20

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Thick

theorem Formalism.BehrendSets.Thick.mul_abs_sub_lt {a b c n : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hna : c * a < n) (hnb : c * b < n) : c * |a - b| < n := by sorry
