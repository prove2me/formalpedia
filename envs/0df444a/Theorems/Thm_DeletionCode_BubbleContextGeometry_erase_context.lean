-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_erase_context
-- name    : DeletionCode.BubbleContextGeometry.erase_context
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:40:09.636762+00:00
-- url     : https://prove2.me/theorems/972d008b-d7b1-471f-b170-2d639e5b5076
-- title:
--   Bubble Context Geometry: erase context
-- statement:
--   The fixed canonical run deletion also works inside arbitrary context.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L50-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L50-L55

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.erase_context {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    (x ++ (bubble.longWord ++ y)).eraseIdx (x.length + editOffset k) =
      x ++ (bubble.shortWord ++ y) := by sorry
