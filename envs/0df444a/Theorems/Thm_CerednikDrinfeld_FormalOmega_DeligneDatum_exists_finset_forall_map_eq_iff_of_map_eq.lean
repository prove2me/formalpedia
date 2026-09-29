-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_forall_map_eq_iff_of_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ad2a2f15-fa98-5a5e-8bd4-6b962d82a636
-- title:
--   Local equation for coincidence of two Deligne data
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with field of fractions $K$, let $\pi \in \mathcal{O}$ be irreducible, and assume the residue ring $\mathcal{O}/(\pi)$ is finite. Let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, and let $d_1, d_2$ be two Deligne data over $B$: each assigns to every full lattice $M \subset K^2$ a $B$-submodule $\mathrm{line}(M) \subseteq B \otimes_{\mathcal{O}} M$ with invertible quotient, compatibly with the base-changed inclusions for $M' \le M$ and with the base-changed homotheties $\mathrm{scalarGL}(c)$, $c \in K^\times$, and satisfying the nondegeneracy condition: for every prime $\mathfrak{p}$ of $B$ there are full lattices $M' \le M$ with $\pi M \subseteq M'$ such that $1 \otimes v \notin \mathrm{line}(M) + \mathfrak{p}\,(B \otimes M)$ for every $v \in M \setminus M'$, and $1 \otimes v' \notin \mathrm{line}(M') + \mathfrak{p}\,(B \otimes M')$ for every $v' \in M'$ not of the form $\pi w$ with $w \in M$. Let $L'$ be a field that is an $\mathcal{O}$-algebra and $\varphi : B \to L'$ an $\mathcal{O}$-algebra map with $d_1$ and $d_2$ having equal base changes along $\varphi$ (`DeligneDatum.map`, formed by taking the span of the image of each line under $\varphi \otimes \mathrm{id}$). The conclusion asserts the existence of $f \in B$ with $\varphi(f) \neq 0$ and a finite subset $s \subseteq B$ such that, for every commutative $\mathcal{O}$-algebra $C$ and every $\mathcal{O}$-algebra map $\chi : B \to C$ with $\chi(f)$ a unit, the base changes of $d_1$ and $d_2$ along $\chi$ coincide if and only if $\chi(b) = 0$ for all $b \in s$.
--
--   In the Deligne-datum description of Drinfeld's formal upper half plane, this is the statement that the diagonal is a closed immersion cut out, Zariski-locally near a point where two sections agree, by finitely many equations: the coincidence locus of two $B$-points becomes, after inverting one function not vanishing at $\varphi$, the common zero locus of a finite set of elements of $B$. It is used in the construction of fine moduli interpretations for the Čerednik–Drinfeld uniformisation, and its proof cites the rigidity statement that a Deligne datum is determined by its lines at the two lattices of an edge chart containing it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_forall_map_eq_iff_of_map_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d₁ d₂ : DeligneDatum (K := K) π B)
    {L' : Type} [Field L'] [Algebra 𝒪 L'] (φ : B →ₐ[𝒪] L') (h : d₁.map π φ = d₂.map π φ) :
    ∃ (f : B) (s : Finset B), φ f ≠ 0 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
        (d₁.map π χ = d₂.map π χ ↔ ∀ b ∈ s, χ b = 0) := by sorry
