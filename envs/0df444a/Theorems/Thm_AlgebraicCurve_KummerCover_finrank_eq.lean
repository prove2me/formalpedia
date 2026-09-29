-- Prove2me | Theorems.Thm_AlgebraicCurve_KummerCover_finrank_eq
-- name    : AlgebraicCurve.KummerCover.finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/f895bb2a-2069-59a3-85d5-6d91b6289bdb
-- title:
--   Splitting field of Xᵖ - f has degree p
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra, let $p$ be a prime, and let $f \in F$. Suppose $L$ is a splitting field over $F$ of the polynomial $X^p - C f$, i.e. this polynomial splits in $L$ and $L$ is generated over $F$ by its roots. Assume further that the set $\mathrm{primitiveRoots}\ p\ F$ of primitive $p$-th roots of unity in $F$ is non-empty, and that $f$ is not a $p$-th power in $F$, in the sense that $g^p \neq f$ for every $g \in F$. Then the $F$-vector space $L$ has finite rank exactly $p$: $\operatorname{finrank}_F L = p$.
--
--   This is the basic degree computation of Kummer theory for a radical extension of prime degree: over a field containing the $p$-th roots of unity, adjoining a $p$-th root of a non-$p$-th-power $f$ gives an extension of degree $p$, which is then automatically the full splitting field. It is used in the construction of Kummer covers of curves, feeding the statements about prolongation of $p$-th roots across a regular local base that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_KummerCover_finrank_eq.lean

import Mathlib.FieldTheory.KummerExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem AlgebraicCurve.KummerCover.finrank_eq {F L : Type*} [Field F] [Field L] [Algebra F L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p ≠ f) :
    Module.finrank F L = p := by sorry
