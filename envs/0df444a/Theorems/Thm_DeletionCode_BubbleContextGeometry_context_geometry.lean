-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_context_geometry
-- name    : DeletionCode.BubbleContextGeometry.context_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:14.055188+00:00
-- url     : https://prove2.me/theorems/988c9c22-ca22-4821-a0f6-94bd0efd7552
-- title:
--   Bubble Context Geometry: context geometry
-- statement:
--   In either orientation, source uniqueness and the actual grammar boundary
--   bits suffice for both simple paths and the endpoint-only intersection.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L138-L149
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L138-L149

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.context_geometry {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.negativeWord ++ y)))
      (x ++ (bubble.negativeWord ++ y)).length k) : Geometry bubble := by sorry
