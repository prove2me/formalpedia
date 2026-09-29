-- Prove2me | Theorems.Thm_FormalGroup_IsBaseChange_map_frobenius
-- name    : FormalGroup.IsBaseChange.map_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/58b505b7-2f5c-5907-aa42-18dbdc5784d6
-- title:
--   Frobenius twist commutes with base change
-- statement:
--   Let $q$ be a prime, and let $R$ and $S$ be commutative rings of characteristic $q$ (in the same universe). Let $F$ be a one-dimensional formal group law over $R$, let $f : R \to S$ be a ring homomorphism, and let $G$ be a one-dimensional formal group law over $S$. Assume that $G$ is the base change of $F$ along $f$, in the sense that the power series underlying $G$ is obtained from the power series underlying $F$ by applying $f$ to each coefficient. Writing $\mathrm{frobenius}\,R\,q$ for the Frobenius endomorphism $x \mapsto x^{q}$ of $R$, and similarly for $S$, and writing $F.\mathrm{map}$ for the formal group law obtained by applying a ring homomorphism to the coefficients of $F$, the conclusion is that the Frobenius twist $F.\mathrm{map}(\mathrm{frobenius}\,R\,q)$ likewise base changes along $f$ to $G.\mathrm{map}(\mathrm{frobenius}\,S\,q)$: the coefficientwise image under $f$ of the former is the power series underlying the latter.
--
--   This is the compatibility of the coefficientwise Frobenius twist of a formal group law with base change along a ring homomorphism in characteristic $q$, a bookkeeping step in the theory of formal group laws over rings of positive characteristic. It is used in the analysis of Drinfeld-type bases and the construction of a trivialising isomorphism in [`FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsBaseChange_map_frobenius.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.IsBaseChange.map_frobenius
    {R S : Type u} [CommRing R] [CommRing S] (q : ℕ) [Fact q.Prime] [CharP R q] [CharP S q]
    (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S) (h : F.IsBaseChange f G) :
    (F.map (frobenius R q)).IsBaseChange f (G.map (frobenius S q)) := by sorry
