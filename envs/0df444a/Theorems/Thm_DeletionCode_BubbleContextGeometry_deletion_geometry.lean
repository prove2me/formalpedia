-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_deletion_geometry
-- name    : DeletionCode.BubbleContextGeometry.deletion_geometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:40:14.278196+00:00
-- url     : https://prove2.me/theorems/fa6c4ef0-e090-4254-b35f-9df44582f853
-- title:
--   Bubble Context Geometry: deletion geometry
-- statement:
--   The Bubble Context Geometry construction uses the deletion geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L79-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L79-L105

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.deletion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.longWord ++ y)))
      (x ++ (bubble.longWord ++ y)).length k) : Geometry bubble := by sorry
