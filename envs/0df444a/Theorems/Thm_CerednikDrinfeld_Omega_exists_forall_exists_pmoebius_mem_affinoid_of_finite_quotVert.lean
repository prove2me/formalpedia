-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert
-- name    : CerednikDrinfeld.Omega.exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/222ce725-b4f0-5e59-8522-d5660533454c
-- title:
--   Fundamental affinoid for a group acting through ρ on the tree
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible and assume the quotient $R/(\varpi)$ is finite, and let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Assume: every element of $R$ has image of valuation $\le 1$ in $K$; conversely every $a\in K_0$ with $v(a)\le 1$ lies in the image of $R$; and for every $\varepsilon\neq 0$ in $\Gamma_0$ some power $v(\varpi)^N\le\varepsilon$. Let $\varpi_1$ be a pseudo-uniformiser of $(K_0,K)$, i.e. an element of $K_0$ with $0<v(\varpi_1)<1$ such that every nonzero $a\in K_0$ satisfies $v(\varpi_1)^N\le v(a)\le v(\varpi_1)^{-N}$ for some $N$, and assume $\varpi_1$ is exhausting: every $z$ in the Drinfeld upper half-plane $\Omega=K\setminus\operatorname{im}(K_0\to K)$ lies in the affinoid $\Omega_n=\{z: v(z)\le v(\varpi_1)^{-n}$ and $v(z-a)\ge v(\varpi_1)^{n}$ for all $a\in K_0$ with $v(a)\le v(\varpi_1)^{-n}\}$ for some $n$. Let $G$ be a group with a homomorphism $\rho: G\to \mathrm{PGL}_2(K_0)$, acting on the set of homothety classes of full $R$-lattices in $K_0^2$ so that adjacency in the Bruhat–Tits tree is preserved, and such that $g\cdot w=\rho(g)\cdot w$ for all $g$ and all vertices $w$; assume the set of $G$-orbits of vertices is finite. Then there is $N\in\mathbb{N}$ such that for every $z\in\Omega$ there is $\gamma\in G$ with $\rho(\gamma)z\in\Omega_N$, the action being the Möbius action on $\mathbb{P}^1(K)$ transported to $K$ (with $\infty$ sent to $0$).
--
--   This is the existence of a fundamental affinoid for a group acting on Drinfeld's upper half-plane through a representation into $\mathrm{PGL}_2(K_0)$ whose induced action on the Bruhat–Tits tree of $(R,K_0)$ has finitely many vertex orbits. It is the form used downstream to show that a $G$-stable subset of $\Omega$ meeting every affinoid in a finite set is finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))] :
    ∃ N : ℕ, ∀ z : ↥(upperHalfPlane K₀ K), ∃ γ : G, pmoebius K₀ (ρ γ) (z : K) ∈ affinoid ϖ₁ N := by sorry
