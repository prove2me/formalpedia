-- Prove2me | Theorems.Thm_D1Bound5_extension_product
-- name    : D1Bound5.extension_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:29:02.609107+00:00
-- url     : https://prove2.me/theorems/c2476b71-67f6-41e7-90f4-bef6813eff9a
-- title:
--   Extension product
-- statement:
--   The product identity at the start of lem:irregular-growth.
-- source:
--   D1Bound5/Regular.lean, lines 20-29, SHA-256 216649d224d94c38aed36aa23129fd314ab8957413daa9e4aa3f53dd8156c10a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.extension_product {R : Type*} [CommRing R] (a b c r s t : R)
    (hr : r ^ 2 = a*b+1) (hs : s ^ 2 = a*c+1) (ht : t ^ 2 = b*c+1) :
    (a+b+c+2*a*b*c+2*r*s*t) * (a+b+c+2*a*b*c-2*r*s*t) =
      regularDefect a b c := by sorry



end D1Bound5
end
