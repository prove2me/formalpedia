-- Prove2me | Theorems.Thm_Bl_b110_goal1
-- name    : Bl.b110.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:10.115809+00:00
-- url     : https://prove2.me/theorems/6ee27037-1308-4e2b-a939-7bc84558d128
-- title:
--   b110: goal1
-- statement:
--   The b110 construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/B110/ExistsMoved.lean#L18-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/B110/ExistsMoved.lean#L18-L54

import Mathlib
import Definitions.Def_Lemmata_B110_ExistsMoved
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.b110

theorem Bl.b110.goal1 :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by sorry
