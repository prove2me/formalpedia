-- Prove2me | Theorems.Thm_AlonTarsi_alon_tarsi
-- name    : AlonTarsi.alon_tarsi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:41.91854+00:00
-- url     : https://prove2.me/theorems/76bc0c87-4adc-4f85-9d15-5c6de3c0725b
-- title:
--   Alon Tarsi: alon tarsi
-- statement:
--   **The Alon–Tarsi theorem (1992).** If an orientation `D` of `G` has different numbers of even
--   and odd Eulerian subdigraphs, then `G` can be properly coloured from any lists `L` with
--   `|L v|` larger than the out-degree of `v` in `D`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L53-L116
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L53-L116

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

theorem AlonTarsi.alon_tarsi {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by sorry
