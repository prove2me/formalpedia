-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_vertex_path_injective
-- name    : DeletionCode.SpectrumPath.vertex_path_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:19:43.503038+00:00
-- url     : https://prove2.me/theorems/208ad8fe-bfe3-4b79-8dbb-8854667b7e5c
-- title:
--   Spectrum Path: vertex path injective
-- statement:
--   All n-L+2 vertices, including the terminal vertex, are distinct.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L88-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L88-L99

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.vertex_path_injective (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) := by sorry
