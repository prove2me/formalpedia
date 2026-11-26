-- Prove2me | Theorems.Thm_AlonTarsi_card_edgeSet_le_of_isPlanar_bipartite
-- name    : AlonTarsi.card_edgeSet_le_of_isPlanar_bipartite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:24:03.635168+00:00
-- url     : https://prove2.me/theorems/07405682-08dc-5158-b1f4-b0d2bf26e47f
-- title:
--   Alon Tarsi: card edge Set le of is Planar bipartite
-- statement:
--   **Euler bound.** A finite planar bipartite graph whose non-isolated vertices have degree at
--   least two has at most twice as many edges as non-isolated vertices.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L136-L150
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean#L136-L150

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
public import Definitions.Def_AlonTarsiLib_PlanarSparse
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open AlonTarsi
variable {V : Type*}

theorem AlonTarsi.card_edgeSet_le_of_isPlanar_bipartite [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] (hP : IsPlanar H) (side : V → Bool)
    (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (hdeg : ∀ v u, H.Adj v u → 2 ≤ Nat.card {w // H.Adj v w}) :
    Nat.card H.edgeSet ≤ 2 * #{v | ∃ u, H.Adj v u} := by sorry
