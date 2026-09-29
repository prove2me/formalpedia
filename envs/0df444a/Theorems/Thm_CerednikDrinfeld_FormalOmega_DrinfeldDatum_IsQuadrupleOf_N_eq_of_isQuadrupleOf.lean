-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9bf3c109-1516-5cde-8e66-6d2758524c96
-- title:
--   Drinfeld lattices determined by the underlying Deligne datum
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$ (an $\mathcal O$-algebra realising the fraction field), let $\pi \in \mathcal O$ be irreducible, and let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum over $B$ for $\pi$, that is, an assignment to every full $\mathcal O$-lattice $M \subset K^2$ of a $B$-submodule $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, monotone under inclusions of lattices, equivariant for scalar homotheties, and nondegenerate at every prime of $B$. Let $Q$ and $Q'$ be Drinfeld data over $B$: each consists of functions $N_0, N_1$ from $\operatorname{Spec} B$ to full lattices in $K^2$ with $N_0(x) \subseteq N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, with open membership loci, together with invertible $B$-modules $T_0, T_1$ and maps $\Pi_0, \Pi_1$ between them composing both ways to multiplication by $\pi$, trivialisations $u_0(x), u_1(x)$ of the stalks of $T_0, T_1$ at each prime $x$ by the base changes of $N_0(x), N_1(x)$ to the local ring at $x$, compatible with the inclusion and with multiplication by $\pi$, and the remaining coherence data. Assume both $Q$ and $Q'$ are quadruples of the same $d$, i.e. for every prime $x$ of $B$ the pair $(N_0(x), N_1(x))$ satisfies Deligne's edge nondegeneracy condition for $d$ at $x$ — $N_0(x) \subseteq N_1(x)$, $\pi N_1(x) \subseteq N_0(x)$, and no $v \in N_1(x) \setminus N_0(x)$ (respectively no $v' \in N_0(x)$ not divisible by $\pi$ in $N_1(x)$) has $1 \otimes v$ lying in $\mathrm{line}(N_1(x)) + x \cdot \top$ (respectively $1 \otimes v'$ in $\mathrm{line}(N_0(x)) + x\cdot\top$) — and the kernels of $u_0(x)$ and $u_1(x)$ are the lines of $d$ base changed to the local ring at $x$ at $N_0(x)$ and $N_1(x)$. The conclusion is that at every prime $x$ of $B$ one has $N_0(x) = N_0'(x)$ and $N_1(x) = N_1'(x)$.
--
--   This is the uniqueness of the simplex carrying a point of the formal upper half plane: the lattice functions of a Drinfeld datum are recovered from the Deligne datum it presents, the scalar homothety relating two candidate edges being killed by the determinant-index normalisation available because $\pi$ is nilpotent in $B$. It is the first half of the comparison of Drinfeld quadruples over a fixed Deligne datum, used in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) (h' : Q'.IsQuadrupleOf d) :
    ∀ x : PrimeSpectrum B, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by sorry
