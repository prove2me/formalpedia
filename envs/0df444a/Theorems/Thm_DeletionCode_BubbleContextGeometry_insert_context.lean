-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_insert_context
-- name    : DeletionCode.BubbleContextGeometry.insert_context
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:34:07.888753+00:00
-- url     : https://prove2.me/theorems/4705ee39-d769-4b1d-9cca-19e38e4979d2
-- title:
--   Bubble Context Geometry: insert context
-- statement:
--   The Bubble Context Geometry construction uses the insert context property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L62-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L62-L77

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.insert_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit =
      listLetters (x ++ (bubble.longWord ++ y)) := by sorry
