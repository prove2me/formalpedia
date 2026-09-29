-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert
-- name    : CerednikDrinfeld.Omega.exists_valuations_invariantFieldOf_of_finite_quotVert
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/06406b98-43da-5841-a560-6d84edeac872
-- title:
--   A proper family of K-rational valuations on Δ-invariant meromorphic functions
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume: $K$ is complete and algebraically closed; the rank-one condition `hrk` holds, i.e. for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$. Let $R_0$ be a discrete valuation domain with fraction field $K_0$ and finite residue field such that the image of $R_0$ in $K_0$ is exactly $\{x : v(x)\le 1\}$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi\in K_0$ with $0<v(\varpi.\varpi)<1$ and such that every nonzero $a\in K_0$ satisfies $v(\varpi.\varpi)^N\le v(a)\le v(\varpi.\varpi)^{-N}$ for some $N$, let $\varpi_0\in R_0$ be irreducible with image $\varpi.\varpi$, and assume `IsExhausted`: every point of the upper half plane $\Omega=K\setminus\operatorname{im}(K_0\to K)$ lies in one of the affinoids $\{z : v(z)\le v(\varpi.\varpi)^{-n}$ and $v(z-a)\ge v(\varpi.\varpi)^{n}$ for all $a\in K_0$ with $v(a)\le v(\varpi.\varpi)^{-n}\}$. Let $G$ be a group with a homomorphism $\rho\colon G\to \mathrm{PGL}_2(K_0)$, acting on the set of homothety classes of full lattices in $K_0^2$ by graph automorphisms of the Bruhat–Tits tree and acting through $\rho$ (that is, $g\cdot w=\rho(g)\cdot w$), and suppose the ring `Omega.HolRingOf ϖ ρ` of functions on $\Omega$ holomorphic on every affinoid is a domain. Let $\Delta\le G$ be such that the stabiliser of every dart of the tree in $\rho(\Delta)$ is finite and the set of $\Delta$-orbits of vertices is finite. Then the invariant field $M=$ `Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ`, a subfield of the fraction field of that ring, admits a set $V$ of $\mathbb Z^{m0}$-valued valuations such that: every $v\in V$ satisfies $v(c)=1$ for every nonzero $c\in K$; every $v\in V$ is $K$-rational in the sense that $v(f)=1$ implies $v(f-c)<1$ for some $c\in K$; for each nonzero $f\in M$ the set of $v\in V$ with $v(f)>1$ is finite; and any $f\in M$ with $v(f)\le 1$ for all $v\in V$ lies in the image of $K$.
--
--   This is the valuative formulation of the compactness of the Mumford quotient $\rho(\Delta)\backslash\Omega$: the family $V$ consists of the orders of vanishing at points of $\Omega$, and the four conditions are exactly those needed to recognise the $\Delta$-invariant meromorphic functions as the function field of a curve over $K$. It is used in the deduction that this invariant field contains a transcendental element over which it is finite, hence is an algebraic function field of one variable over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups WithZero
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_valuations_invariantFieldOf_of_finite_quotVert

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Δ : Subgroup G)
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Δ.map ρ)) d))
    [Finite (Mumford.QuotVert Δ (LT.LatticeTree.Vertex R₀ K₀))] :
    ∃ V : Set (Valuation ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) ℤᵐ⁰),
      (∀ v ∈ V, ∀ c : K, c ≠ 0 →
        v (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) c) = 1) ∧
      (∀ v ∈ V, ∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), v f = 1 →
        ∃ c : K, v (f - algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) c) < 1) ∧
      (∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), f ≠ 0 → {v ∈ V | 1 < v f}.Finite) ∧
      (∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), (∀ v ∈ V, v f ≤ 1) →
        f ∈ Set.range (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ))) := by sorry
