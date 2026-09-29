-- Prove2me | Theorems.Thm_BraidsLinksMCG_path_cast_eq_of_pointwise_child_v2
-- name    : BraidsLinksMCG.path_cast_eq_of_pointwise_child_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T16:31:07.399552+00:00
-- url     : https://prove2.me/theorems/244b49e5-893a-4429-b34d-dcd9c852e668
-- title:
--   Path casts agree under pointwise equality
-- statement:
--   Two paths with equal values at every parameter are equal after casting the first path's endpoints to the endpoints of the second path.
-- source:
--   Minimal reusable path-cast sublemma extracted from extensionAlphaPath_one_cast in candidate 2456 for open leaf 2273a291-a4e8-a43a-8b38-b527095999a64. It isolates the endpoint-cast and path-extensionality step without copying unrelated strand-extension geometry.

import Mathlib
namespace BraidsLinksMCG
theorem path_cast_eq_of_pointwise_child_v2 {X : Type*} [TopologicalSpace X] {a b c d : X} (p : Path a b) (q : Path c d) (hc : c = a) (hd : d = b) (h : ∀ t, p t = q t) : p.cast hc hd = q := by sorry
end BraidsLinksMCG
