-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
-- name    : AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/fcaa3ec8-6b29-5e72-9691-999cfbd6a550
-- title:
--   Preimage of a place along a ring homomorphism of fields
-- statement:
--   Let $K$, $F$, $K'$, $F'$ be fields with $F$ a $K$-algebra and $F'$ a $K'$-algebra, and let $\iota : F \to F'$ be a ring homomorphism. Let $w$ be a place of $F'$ over $K'$ in the sense of the project's structure `Place`, that is, a valuation subring $\mathcal{O}_w =$ `w.toValuationSubring` of $F'$ such that $\mathcal{O}_w$ contains $\mathrm{algebraMap}\,K'\,F'(a)$ for every $a \in K'$, $\mathcal{O}_w \neq F'$, and the ring $\mathcal{O}_w$ is a principal ideal ring. Assume that $\iota(\mathrm{algebraMap}\,K\,F(a)) \in \mathcal{O}_w$ for every $a \in K$, and that the preimage valuation subring $\iota^{-1}(\mathcal{O}_w) =$ `w.toValuationSubring.comap ι` is not the whole of $F$. Then there exists a place $v$ of $F$ over $K$, i.e. a valuation subring of $F$ containing the image of $K$, proper, and a principal ideal ring, whose underlying valuation subring is exactly $\iota^{-1}(\mathcal{O}_w)$. No uniqueness assertion is made, and no algebraicity or finiteness is assumed of $\iota$ or of the extensions involved.
--
--   This is the restriction of a place along a homomorphism of fields: the preimage of the valuation ring of $w$ is again the valuation ring of a place, the properness hypothesis being the only obstruction (it is automatic when $F'$ is algebraic over $\iota(F)$, but not for constant field extensions with transcendental constants). It is used in the treatment of constant field extensions of curves, for instance in comparing orders of vanishing and regularity of functions and differentials after base change to an algebraically closed field of constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    (ι : F →+* F') (w : Place K' F')
    (hK : ∀ a : K, ι (algebraMap K F a) ∈ w.toValuationSubring)
    (hne : w.toValuationSubring.comap ι ≠ ⊤) :
    ∃ v : Place K F, v.toValuationSubring = w.toValuationSubring.comap ι := by sorry
