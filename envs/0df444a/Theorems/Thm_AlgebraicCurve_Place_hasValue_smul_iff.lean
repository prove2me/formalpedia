-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_hasValue_smul_iff
-- name    : AlgebraicCurve.Place.hasValue_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/4df92e44-3011-5834-be44-771ef32a524d
-- title:
--   Values at places are transported by automorphisms
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $F$, let $v$ be a place of $F$ over $K$ — that is, a valuation subring $\mathcal{O}_v$ of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring — and let $g \in F$, $a \in K$. Here $\sigma \bullet v$ denotes the place obtained from $v$ by the pointwise action of the automorphism group, whose valuation subring is $\sigma(\mathcal{O}_v)$. For a place $w$, the assertion that $x \in F$ has value $a$ at $w$ means that $x$ lies in $\mathcal{O}_w$ and that the residue of $x$ in the residue field of $\mathcal{O}_w$ equals the image of $a$ under the structure map $K \to \mathcal{O}_w/\mathfrak{m}_w$. The theorem states the equivalence: $\sigma g$ has value $a$ at $\sigma \bullet v$ if and only if $g$ has value $a$ at $v$.
--
--   This is the transport of the notion of the value of a function at a place along a $K$-automorphism of the function field, the companion for values of the corresponding statement for orders of vanishing. It is used in the analysis of places of modular curves, for instance to match the two cuspidal charts of $X_0(q)$ under the Atkin–Lehner involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_hasValue_smul_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.hasValue_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by sorry
