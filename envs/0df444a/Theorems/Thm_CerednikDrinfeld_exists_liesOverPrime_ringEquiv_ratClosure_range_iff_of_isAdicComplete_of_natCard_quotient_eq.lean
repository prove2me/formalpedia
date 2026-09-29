-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq
-- name    : CerednikDrinfeld.exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/62871258-c664-57ae-a8e5-32e1ada311a9
-- title:
--   Unramified complete base realised as the closure of ℚ
-- statement:
--   Let $r$ be a natural number carrying a `Fact` that it is prime. Let $\mathcal{O}$ be a commutative ring which is a domain of characteristic $0$, assumed to be a discrete valuation ring, let $\pi \in \mathcal{O}$ be irreducible, assume $\mathcal{O}$ is adically complete for the ideal $(\pi)$, that the residue ring $\mathcal{O}/(\pi)$ has exactly $r$ elements, and that $(r) = (\pi)$ as ideals of $\mathcal{O}$ (absolute unramifiedness). Let $K_0$ be a field of characteristic $0$ which is a fraction field of $\mathcal{O}$ via a given algebra structure. The conclusion asserts the existence of a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that the image of $r$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (the predicate `LiesOverPrime r`, so that $A$ is a place above $r$), together with a ring isomorphism $e$ from $K_0$ onto `ratClosure A`, the topological closure of the bottom subfield inside the completion `A.valuation.Completion` of $\overline{\mathbb{Q}}$ for the valuation of $A$, with the property that for every $x$ in `ratClosure A`: $x$ lies in the range of $\mathcal{O} \to K_0$ followed by $e$ if and only if the valuation of the image of $x$ in `A.valuation.Completion` is at most $1$. Thus $e$ identifies $\mathcal{O}$ with the valuation ring of the closure of $\mathbb{Q}$ in that completion.
--
--   This identifies an abstract absolutely unramified complete discrete valuation ring with residue cardinality $r$, together with its fraction field, with the valuation ring and the closure of $\mathbb{Q}$ inside the completion of $\overline{\mathbb{Q}}$ at a place above $r$ — the Witt-vector description $W(\mathbb{F}_r) = \mathbb{Z}_r$ in the form needed for coefficient fields sitting inside a fixed algebraic closure. It is used in the Čerednik–Drinfeld part of the development, by [`CerednikDrinfeld.evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd`](thm.html#CerednikDrinfeld.evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq.lean

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField ValuationSubring

theorem CerednikDrinfeld.exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq
    (r : ℕ) [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime r) (e : K₀ ≃+* ↥(ratClosure A)),
      ∀ x : ↥(ratClosure A), x ∈ Set.range (e.toRingHom.comp (algebraMap 𝒪 K₀)) ↔
        Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1 := by sorry
