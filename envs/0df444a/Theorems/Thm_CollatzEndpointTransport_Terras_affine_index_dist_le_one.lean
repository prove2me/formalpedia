-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affine_index_dist_le_one
-- name    : CollatzEndpointTransport.Terras.affine_index_dist_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:25:44.57189+00:00
-- url     : https://prove2.me/theorems/50a7676b-4268-4999-864d-33c568917bac
-- title:
--   Terras: affine index dist le one
-- statement:
--   Elementary affine-strip lemma: if the coefficient scale `A` is at
--   least the target width `D`, translated points with offsets in `[0,A)` can
--   be `D`-close only at equal or adjacent indices.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L241-L280
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L241-L280

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affine_index_dist_le_one
    {A D q r i j : ℕ}
    (hA : D ≤ A) (hq : q < A) (hr : r < A)
    (hclose : (A * i + q).dist (A * j + r) < D) :
    i.dist j ≤ 1 := by sorry
