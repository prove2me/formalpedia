-- Prove2me | Theorems.Thm_AlonTarsi_choosable_three_of_isPlanar_bipartite
-- name    : AlonTarsi.choosable_three_of_isPlanar_bipartite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:56.494635+00:00
-- url     : https://prove2.me/theorems/4311b372-3581-47d3-8163-0864f4aa972f
-- title:
--   Alon Tarsi: choosable three of is Planar bipartite
-- statement:
--   **Alon–Tarsi (1992).** Every finite planar bipartite graph is 3-choosable.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L212-L239
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L212-L239

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Definitions.Def_AlonTarsiLib_PlanarSparse
public import Definitions.Def_AlonTarsiLib_AlonTarsi
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem AlonTarsi.choosable_three_of_isPlanar_bipartite [Finite V] {Color : Type*} (G : SimpleGraph V)
    (hP : LeanPool.K5MinorFreeChoosability.IsPlanar G) (hB : G.Colorable 2)
    (L : V → Finset Color) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by sorry
