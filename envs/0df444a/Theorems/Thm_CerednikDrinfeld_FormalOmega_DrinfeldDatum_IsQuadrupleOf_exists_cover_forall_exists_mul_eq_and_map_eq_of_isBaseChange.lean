-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/4ab930c7-7c9d-5405-9a7a-41f54fe438b1
-- title:
--   Zariski-local lifting of Pi-coordinates with α'β'=π
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$, let $\pi\in\mathcal O$ be irreducible and assume the residue ring $\mathcal O/(\pi)$ is finite. Let $B$ and $B'$ be commutative $\mathcal O$-algebras and $\varphi\colon B'\to B$ a surjective $\mathcal O$-algebra map whose kernel is a nilpotent ideal, and suppose the image of $\pi$ in $B'$ is nilpotent. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ (families of full $\mathcal O$-lattices $N_0(x)\le N_1(x)$ in $K^2$ indexed by the primes of $B$ with $\pi N_1\subseteq N_0$ and the usual openness conditions, invertible $B$-modules $T_0,T_1$ with $B$-maps $\Pi_0\colon T_0\to T_1$, $\Pi_1\colon T_1\to T_0$ whose two composites are multiplication by $\pi$, together with the stalkwise maps $u_0,u_1$ from the base-changed lattices), let $d$ be a Deligne datum over $B$ (a line $d.\mathrm{line}(M)\subseteq B\otimes_{\mathcal O}M$ for each full lattice $M$, with invertible quotient, monotone in $M$, equivariant for homotheties and nondegenerate at every prime of $B$), and assume `Q.IsQuadrupleOf d`: at each prime $x$ of $B$ the datum $d$ satisfies the edge-nondegeneracy condition at $x$ for the lattices $Q.L_0(x),Q.L_1(x)$, and the kernels of $u_0(x)$ and $u_1(x)$ are the lines of the localised datum at those two lattices. Fix $e_0\in T_0$ and $e_1\in T_1$ such that every element of $T_0$ is $b\cdot e_0$ for a unique $b\in B$ and likewise for $T_1$ and $e_1$, and let $\alpha,\beta\in B$ satisfy $\Pi_0e_0=\alpha e_1$ and $\Pi_1e_1=\beta e_0$. Finally let $d'$ be a Deligne datum over $B'$ whose base change along $\varphi$ is $d$, i.e. for every full lattice $M$ the line $d.\mathrm{line}(M)$ is the $B$-span of the image of $d'.\mathrm{line}(M)$ under $\varphi\otimes\mathrm{id}_M$. Then there are $n\in\mathbb N$ and $f\colon \mathrm{Fin}\,n\to B'$ with $(f_0,\dots,f_{n-1})=B'$ such that for every index $i$, every commutative ring $L'$ which is a localisation of $B'$ away from $f_i$, every commutative ring $L$ which is a localisation of $B$ away from $\varphi(f_i)$, and every ring homomorphism $\varphi_L\colon L'\to L$ with $\varphi_L\circ(B'\to L')=(B\to L)\circ\varphi$, there exist $\alpha',\beta'\in L'$ with $\varphi_L(\alpha')$ the image of $\alpha$ in $L$, $\varphi_L(\beta')$ the image of $\beta$ in $L$, and $\alpha'\beta'$ equal to the image in $L'$ of the element $\pi$ of $B'$.
--
--   This is the covering form of the local coordinate-lifting step for Drinfeld quadruples on the formal Čerednik–Drinfeld model: the pair $(\alpha,\beta)$ of $\Pi$-coordinates on a quadruple over $B$, with product $\pi$, can be lifted along an infinitesimal surjection $B'\to B$ after passing to a Zariski cover of $\operatorname{Spec}B'$, provided the Deligne datum itself already lifts. It is used in the construction of the period map for the special formal modules, where the lifted coordinates are compared with the chart coordinates on the formal upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    (φ : B' →ₐ[𝒪] B) (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker (φ : B' →+* B)))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (hQ : Q.IsQuadrupleOf d)
    (e₀ : Q.T₀) (e₁ : Q.T₁)
    (he₀ : ∀ t : Q.T₀, ∃! b : B, t = b • e₀) (he₁ : ∀ t : Q.T₁, ∃! b : B, t = b • e₁)
    (α β : B) (hα : Q.Pi₀ e₀ = α • e₁) (hβ : Q.Pi₁ e₁ = β • e₀)
    (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) :
    ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L' : Type) [CommRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
        (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
        (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B)),
        ∃ α' β' : L', φL α' = algebraMap B L α ∧ φL β' = algebraMap B L β ∧
          α' * β' = algebraMap B' L' (algebraMap 𝒪 B' π) := by sorry
