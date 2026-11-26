-- Prove2me | Theorems.Thm_AlonTarsi_exists_orientation_card_le_two
-- name    : AlonTarsi.exists_orientation_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:27.694917+00:00
-- url     : https://prove2.me/theorems/3834d0de-bbca-5d80-a53b-985439ba520e
-- title:
--   Alon Tarsi: exists orientation card le two
-- statement:
--   **Hakimi's lemma** (for out-degree two), via Hall's theorem: if every set of edges spans at
--   least half as many vertices as it has edges, then `G` has an orientation with all out-degrees at
--   most two.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L122-L166
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean#L122-L166

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

theorem AlonTarsi.exists_orientation_card_le_two (G : SimpleGraph V)
    (hsp : ∀ s : Finset (Sym2 V), (∀ e ∈ s, e ∈ G.edgeSet) → #s ≤ 2 * #{v | ∃ e ∈ s, v ∈ e}) :
    ∃ D : V → V → Prop, IsOrientation G D ∧ ∀ v, #{w | D v w} ≤ 2 := by sorry
