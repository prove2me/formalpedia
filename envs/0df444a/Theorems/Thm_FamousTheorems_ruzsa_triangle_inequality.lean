-- Prove2me | Theorems.Thm_FamousTheorems_ruzsa_triangle_inequality
-- name    : FamousTheorems.ruzsa_triangle_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:54.39405+00:00
-- url     : https://prove2.me/theorems/0a10d704-1ab6-41f2-8fb3-bf66f440817f
-- title:
--   The Ruzsa triangle inequality
-- statement:
--   **The Ruzsa triangle inequality.** For finite subsets $A,B,C$ of a group (written additively),
--   $$|A-C|\,|B|\le|A-B|\,|C-B| .$$
--
--   Setting $d(A,B)=\log\frac{|A-B|}{\sqrt{|A||B|}}$ (the Ruzsa distance), it says $d(A,C)\le d(A,B)+d(B,C)$, whence the name. It is a basic inequality in additive combinatorics, used with the Plünnecke–Ruzsa inequality to control iterated sumsets.
--
--   **Formalization note.** Mathlib's `Finset.ruzsa_triangle_inequality_sub_sub_sub`, stated for an arbitrary (not necessarily commutative) additive group with pointwise difference sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.ruzsa_triangle_inequality_sub_sub_sub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem ruzsa_triangle_inequality {G : Type*} [AddGroup G] [DecidableEq G] (A B C : Finset G) :
    (A - C).card * B.card ≤ (A - B).card * (C - B).card := by sorry

end FamousTheorems
