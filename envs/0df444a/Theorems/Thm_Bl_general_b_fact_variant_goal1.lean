-- Prove2me | Theorems.Thm_Bl_general_b_fact_variant_goal1
-- name    : Bl.general_b_fact_variant.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:46.01582+00:00
-- url     : https://prove2.me/theorems/82350a03-7a35-4351-9f46-5c8ae9f6b901
-- title:
--   general b fact variant: goal1
-- statement:
--   The general b fact variant construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactVariant/Imports.lean#L5-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactVariant/Imports.lean#L5-L56

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_variant

theorem Bl.general_b_fact_variant.goal1 :
  ∀ {n : Nat} {N N' B B' : Matrix.{0, 0, 0} (Fin n) (Fin n) Complex},
  Matrix.BlockTriangular.{0, 0, 0} N (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
    Matrix.BlockTriangular.{0, 0, 0} N' (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
      (∀ (i : Fin n), Eq.{1} (N i i) 1) →
        (∀ (i : Fin n), Eq.{1} (N' i i) 1) →
          Matrix.BlockTriangular.{0, 0, 0} B id.{1} →
            Matrix.BlockTriangular.{0, 0, 0} B' id.{1} →
              Ne.{1} (Matrix.det.{0, 0} B) 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N B) (HMul.hMul.{0, 0, 0} N' B') → Eq.{1} N N' := by sorry
