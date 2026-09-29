-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime
-- name    : AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/a4f896aa-4f8f-571b-a776-3611ac84ab28
-- title:
--   Specℚ̄toSpec𝒪 is an open immersion
-- statement:
--   Let $\mathcal O$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$, and let $p$ be a natural number which is prime. Assume that $\mathcal O$ lies over $p$ in the sense of the project predicate `LiesOverPrime`, that is, the image of $p$ under the canonical map $\mathbb N \to \overline{\mathbb Q}$ belongs to the set of non-units of $\mathcal O$ (the maximal ideal of the valuation ring, viewed inside $\overline{\mathbb Q}$). The inclusion $\mathcal O \hookrightarrow \overline{\mathbb Q}$, regarded as a morphism of commutative rings, induces a morphism of schemes $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec}\mathcal O$; the conclusion asserts that this morphism is an open immersion. Concretely, its image is the basic open subset $D(p) \subseteq \operatorname{Spec}\mathcal O$, and $\operatorname{Spec}\overline{\mathbb Q}$ is isomorphic over $\operatorname{Spec}\mathcal O$ to that open subscheme.
--
--   Valuation subrings of $\overline{\mathbb Q}$ whose maximal ideal contains $p$ behave, for this purpose, like rings with $\overline{\mathbb Q} = \mathcal O[1/p]$, so the generic point is an open point of $\operatorname{Spec}\mathcal O$; this is what makes base change to the generic fibre an open immersion. The statement is used in the study of smooth relative curves over such valuation subrings, in the constructions producing a valuation subring with prescribed order and residue data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry

theorem AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) := by sorry
