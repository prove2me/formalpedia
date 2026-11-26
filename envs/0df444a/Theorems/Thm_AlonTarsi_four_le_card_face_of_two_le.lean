-- Prove2me | Theorems.Thm_AlonTarsi_four_le_card_face_of_two_le
-- name    : AlonTarsi.four_le_card_face_of_two_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:42.139934+00:00
-- url     : https://prove2.me/theorems/93c76016-7ce6-5c68-864f-1df13c73fc40
-- title:
--   Alon Tarsi: four le card face of two le
-- statement:
--   Variant of `four_le_card_face` requiring degree at least two only at non-isolated
--   vertices: in a bipartite graph, every face has length at least four.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L78-L110
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L78-L110

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

theorem AlonTarsi.four_le_card_face_of_two_le [Finite V]
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w})
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v) (d : H.Dart) :
    4 ≤ Nat.card {e // SameCycle (σ * dartSymm H) d e} := by sorry
