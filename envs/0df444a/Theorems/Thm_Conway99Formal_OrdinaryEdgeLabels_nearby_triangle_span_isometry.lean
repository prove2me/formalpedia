-- Prove2me | Theorems.Thm_Conway99Formal_OrdinaryEdgeLabels_nearby_triangle_span_isometry
-- name    : Conway99Formal.OrdinaryEdgeLabels.nearby_triangle_span_isometry
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:27:28.174793+00:00
-- url     : https://prove2.me/theorems/cf4c6e36-ff8e-4132-8b4d-cae4b6926f72
-- title:
--   Individual nearby triangle span isometry for an ordinary Conway operator
-- statement:
--   For a hypothetical SRG(99,14,1,2) equipped with one actual point frame, literal triangle cubic, ordinary operator, and the explicit minimum-coset/lattice bridge facts in OrdinaryData, every actual triangle meeting the marked closed neighborhood has its whole three-point span isometric under that operator. This is a conditional necessary statement for one triangle. It does not assert the count of 91, cross-span or nonedge isometry, or existence of an ordinary vertex.
-- source:
--   archive/clean-start/proof-library.zip member proofs/ROOTLESS_MINIMUM_DYADS.md sections 1-5; source hash and missing bridges in claims.json. Checked local proof: server-package/Solutions/Sol_NearbySpan.lean.

import Definitions.Def_Conway99_OrdinaryEdgeLabels_20261003
set_option autoImplicit false
open Conway99Formal.OrdinaryEdgeLabels

theorem Conway99Formal.OrdinaryEdgeLabels.nearby_triangle_span_isometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : OrdinaryData G) (a b c : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hnear : a = d.ordinary ∨ G.Adj d.ordinary a) :
    ∀ x ∈ Submodule.span ℝ ({d.point a, d.point b, d.point c} : Set Space),
      ∀ y ∈ Submodule.span ℝ ({d.point a, d.point b, d.point c} : Set Space),
        inner ℝ (d.op d.ordinary x) (d.op d.ordinary y) = inner ℝ x y := by sorry
