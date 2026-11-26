-- Prove2me | Theorems.Thm_AlonTarsi_isPlanar_of_le
-- name    : AlonTarsi.isPlanar_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:18.772606+00:00
-- url     : https://prove2.me/theorems/f8942646-b31e-55c2-aa88-bdb66860d0b8
-- title:
--   Alon Tarsi: is Planar of le
-- statement:
--   A subgraph of a finite planar graph is planar.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L32-L41
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L32-L41

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
public import Definitions.Def_AlonTarsiLib_PlanarSparse
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.isPlanar_of_le [Finite V] {G H : SimpleGraph V} (hG : IsPlanar G) (h : H ≤ G) :
    IsPlanar H := by sorry
