-- Prove2me | Theorems.Thm_AlonTarsi_cycleCount_le_card_nonisolated
-- name    : AlonTarsi.cycleCount_le_card_nonisolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:06.659797+00:00
-- url     : https://prove2.me/theorems/a0a4b47f-a244-4b38-8088-80f835b1d404
-- title:
--   Alon Tarsi: cycle Count le card nonisolated
-- statement:
--   The rotation cycles are indexed by the non-isolated vertices.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L113-L130
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L113-L130

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
public import Definitions.Def_AlonTarsiLib_PlanarSparse
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open AlonTarsi
variable {V : Type*}
variable {H : SimpleGraph V} {σ : Perm H.Dart} (hσ : IsRotationSystem H σ)
include hσ

theorem AlonTarsi.cycleCount_le_card_nonisolated [Fintype V] [DecidableRel H.Adj] :
    cycleCount σ ≤ #{v | ∃ u, H.Adj v u} := by sorry
