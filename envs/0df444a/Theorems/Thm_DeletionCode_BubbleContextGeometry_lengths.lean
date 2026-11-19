-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_lengths
-- name    : DeletionCode.BubbleContextGeometry.lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:25:28.312183+00:00
-- url     : https://prove2.me/theorems/5be4a402-0555-4788-896e-b6c948104259
-- title:
--   Bubble Context Geometry: lengths
-- statement:
--   The Bubble Context Geometry construction uses the lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L36-L42
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L36-L42

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.lengths {k : ℕ} (bubble : BubbleWord k) :
    bubble.shortWord.length + 1 = bubble.longWord.length := by sorry
