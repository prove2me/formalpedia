-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_delete_context
-- name    : DeletionCode.BubbleContextGeometry.delete_context
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:25:23.82502+00:00
-- url     : https://prove2.me/theorems/1af93216-e703-46b4-89bc-a7811667ca6d
-- title:
--   Bubble Context Geometry: delete context
-- statement:
--   The Bubble Context Geometry construction uses the delete context property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L57-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L57-L60

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.delete_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    deleteAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k) =
      listLetters (x ++ (bubble.shortWord ++ y)) := by sorry
