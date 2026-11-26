-- Prove2me | Theorems.Thm_AlonTarsi_face_face_ne_self_of_two_le
-- name    : AlonTarsi.face_face_ne_self_of_two_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:24:00.513912+00:00
-- url     : https://prove2.me/theorems/1a81df05-f924-43b5-8a80-27fe562fa58e
-- title:
--   Alon Tarsi: face face ne self of two le
-- statement:
--   Variant of `face_face_ne_self` requiring degree at least two only at non-isolated
--   vertices.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L50-L74
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L50-L74

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

theorem AlonTarsi.face_face_ne_self_of_two_le [Finite V]
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w})
    (d : H.Dart) : (σ * dartSymm H) ((σ * dartSymm H) d) ≠ d := by sorry
