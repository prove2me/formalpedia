-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_not_mem_iff_ord_neg
-- name    : AlgebraicCurve.Place.not_mem_iff_ord_neg
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:29.79634+00:00
-- url     : https://prove2.me/theorems/18a2ca88-68f6-4847-ae6d-ba01cda19fd0
-- title:
--   A function lies outside a place's valuation ring exactly when it has negative order
-- statement:
--   Let $F/K$ be a field extension, let $v$ be a place of $F$ over $K$, and let $f∈F$. Then $$f∉\mathcal O_v\iff ord_v(f)<0.$$ This translates valuation-ring membership into the order language used for cusps and modular units.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false
open AlgebraicCurve
open AlgebraicCurve.Place

theorem AlgebraicCurve.Place.not_mem_iff_ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) : f ∉ v.toValuationSubring ↔ v.ord f < 0 := by sorry
