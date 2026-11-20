-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_insertion_geometry
-- name    : DeletionCode.BubbleContextGeometry.insertion_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:19.042583+00:00
-- url     : https://prove2.me/theorems/c940a97a-5cb6-43d4-994a-926dee79fc7e
-- title:
--   Bubble Context Geometry: insertion geometry
-- statement:
--   The Bubble Context Geometry construction uses the insertion geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L107-L134
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L107-L134

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.insertion_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.shortWord ++ y)))
      (x ++ (bubble.shortWord ++ y)).length k) : Geometry bubble := by sorry
