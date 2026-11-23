-- Prove2me | Theorems.Thm_Bl_general_b_fact_ter_goal1
-- name    : Bl.general_b_fact_ter.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.130664+00:00
-- url     : https://prove2.me/theorems/0f9d1a14-fd52-44c9-bf84-4d6565e9af4e
-- title:
--   general b fact ter: goal1
-- statement:
--   The general b fact ter construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTer/Imports.lean#L5-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTer/Imports.lean#L5-L58

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_ter

theorem Bl.general_b_fact_ter.goal1 :
  ∀ {r : Nat} {N N' B B' : Matrix.{0, 0, 0} (Fin r) (Fin r) Complex},
  (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N a c) 0) →
    (∀ (a : Fin r), Eq.{1} (N a a) 1) →
      (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N' a c) 0) →
        (∀ (a : Fin r), Eq.{1} (N' a a) 1) →
          (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B a c) 0) →
            (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B' a c) 0) →
              Ne.{1} (Matrix.det.{0, 0} B) 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N B) (HMul.hMul.{0, 0, 0} N' B') → Eq.{1} N N'  := by sorry
