-- Prove2me | Theorems.Thm_AlonTarsi_card_le_two_mul_card_verts
-- name    : AlonTarsi.card_le_two_mul_card_verts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:24:11.510799+00:00
-- url     : https://prove2.me/theorems/34f97e5e-85c3-576f-b341-c5662e4f5670
-- title:
--   Alon Tarsi: card le two mul card verts
-- statement:
--   **Sparsity of planar bipartite graphs.** Every set `s` of edges of a finite planar
--   bipartite graph has at most twice as many edges as vertices incident to them.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L154-L222
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L154-L222

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
public import Definitions.Def_AlonTarsiLib_PlanarSparse
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.card_le_two_mul_card_verts [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hP : IsPlanar G) (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) :
    ∀ s : Finset (Sym2 V), (∀ e ∈ s, e ∈ G.edgeSet) → #s ≤ 2 * #{v | ∃ e ∈ s, v ∈ e} := by sorry
