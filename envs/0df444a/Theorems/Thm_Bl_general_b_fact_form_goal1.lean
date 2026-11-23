-- Prove2me | Theorems.Thm_Bl_general_b_fact_form_goal1
-- name    : Bl.general_b_fact_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:36.880866+00:00
-- url     : https://prove2.me/theorems/1231db94-c959-4a12-ad6d-9300f651f6f4
-- title:
--   general b fact form: goal1
-- statement:
--   The general b fact form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactForm/Imports.lean#L5-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactForm/Imports.lean#L5-L72

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_form

theorem Bl.general_b_fact_form.goal1 :
  ∀ {n : Nat} {N N' U U' : Matrix.{0, 0, 0} (Fin n) (Fin n) Complex},
  Matrix.BlockTriangular.{0, 0, 0} N (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
    (∀ (a : Fin n), Eq.{1} (N a a) 1) →
      Matrix.BlockTriangular.{0, 0, 0} N' (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
        (∀ (a : Fin n), Eq.{1} (N' a a) 1) →
          Matrix.BlockTriangular.{0, 0, 0} U id.{1} →
            Matrix.BlockTriangular.{0, 0, 0} U' id.{1} →
              Ne.{1} (Matrix.det.{0, 0} U') 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N U) (HMul.hMul.{0, 0, 0} N' U') → And (Eq.{1} N N') (Eq.{1} U U') := by sorry
