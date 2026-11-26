-- Prove2me | Theorems.Thm_AlonTarsi_eulerianCount_one_eq_zero
-- name    : AlonTarsi.eulerianCount_one_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:01.123885+00:00
-- url     : https://prove2.me/theorems/2db0bab2-a44c-45f6-96e9-5a41acfdeedc
-- title:
--   Alon Tarsi: eulerian Count one eq zero
-- statement:
--   In an orientation of a bipartite graph there are no odd Eulerian subdigraphs.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L170-L208
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L170-L208

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
open Classical

theorem AlonTarsi.eulerianCount_one_eq_zero (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) :
    eulerianCount D 1 = 0 := by sorry
