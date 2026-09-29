-- Prove2me | Theorems.Thm_BraidsLinksMCG_path_cast_eq_of_subtype_value_child_v1
-- name    : BraidsLinksMCG.path_cast_eq_of_subtype_value_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T17:13:12.507302+00:00
-- url     : https://prove2.me/theorems/8c61f76c-1a73-498f-b5d9-3df3e8655552
-- title:
--   Casted subtype paths agree from pointwise value equality
-- statement:
--   For paths in a subtype, equality of the underlying values at every parameter implies equality after matching the endpoints by casts.
-- source:
--   Focused source-backed child for extensionAlphaPath_one_cast in open leaf 2273a291-a4e8-43a8-b38b-527095999a64. Candidate 2462 isolated the remaining obligation to subtype-path pointwise equality after the general path-cast child was accepted; this child factors out that reusable extensionality step.

import Mathlib
import Theorems.Thm_BraidsLinksMCG_path_cast_eq_of_pointwise_child_v2
namespace BraidsLinksMCG
theorem path_cast_eq_of_subtype_value_child_v1 {X : Type*} [TopologicalSpace X] {P : X → Prop} {a b c d : {x : X // P x}} (p : Path a b) (q : Path c d) (hc : c = a) (hd : d = b) (h : ∀ t, (p t).val = (q t).val) : p.cast hc hd = q := by sorry
end BraidsLinksMCG
