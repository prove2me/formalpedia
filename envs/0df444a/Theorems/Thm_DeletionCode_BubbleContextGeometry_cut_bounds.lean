-- Prove2me | Theorems.Thm_DeletionCode_BubbleContextGeometry_cut_bounds
-- name    : DeletionCode.BubbleContextGeometry.cut_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:25:43.965018+00:00
-- url     : https://prove2.me/theorems/9fbe70f0-b3ad-4689-8506-daf72f9e8f41
-- title:
--   Bubble Context Geometry: cut bounds
-- statement:
--   The Bubble Context Geometry construction uses the cut bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L28-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleContextGeometry.lean#L28-L34

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization

theorem DeletionCode.BubbleContextGeometry.cut_bounds {k : ℕ} (bubble : BubbleWord k) :
    editOffset k < bubble.longWord.length ∧ editOffset k ≤ bubble.shortWord.length := by sorry
