-- Prove2me | Theorems.Thm_DeletionCode_ScriptRigidity_within_one_vertex_path_injective
-- name    : DeletionCode.ScriptRigidity.within_one_vertex_path_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:39.233713+00:00
-- url     : https://prove2.me/theorems/058daab9-9686-43f6-97ee-60101a76deeb
-- title:
--   Script Rigidity: within one vertex path injective
-- statement:
--   The de Bruijn walk after one edit is simple, including its endpoint vertices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L53-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L53-L59

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.ScriptRigidity.within_one_vertex_path_injective {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y)
    (hlen : windowLength k ≤ y.length) :
    Function.Injective (fun i : Fin (y.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters y) (windowLength k) i.val) := by sorry
