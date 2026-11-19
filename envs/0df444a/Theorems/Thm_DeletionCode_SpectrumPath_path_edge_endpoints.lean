-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_path_edge_endpoints
-- name    : DeletionCode.SpectrumPath.path_edge_endpoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:23:02.638295+00:00
-- url     : https://prove2.me/theorems/f8b23cf9-98c5-4e11-887a-7642a938c239
-- title:
--   Spectrum Path: path edge endpoints
-- statement:
--   Each supported gram is the directed edge between the displayed consecutive vertices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L112-L120
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L112-L120

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.path_edge_endpoints (word : Letters) (L i : ℕ) :
    gramPrefix (gram word L i) = vertexAt word L i ∧
      gramSuffix (gram word L i) = vertexAt word L (i + 1) := by sorry
