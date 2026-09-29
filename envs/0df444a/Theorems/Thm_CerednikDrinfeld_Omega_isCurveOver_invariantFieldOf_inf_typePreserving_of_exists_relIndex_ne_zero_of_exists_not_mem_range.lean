-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
-- name    : CerednikDrinfeld.Omega.isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e028cb5d-c013-5d0d-bb02-2e5c50f08be2
-- title:
--   Invariant field of the type-preserving part is a curve field
-- statement:
--   Let $K_0$ be a field and $K$ a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to: the rank condition `hrk`, that for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$; $K$ complete and algebraically closed. Let $R_0$ be a discrete valuation domain with $K_0$ as fraction field and finite residue field, such that `hR₀`: an element of $K_0$ lies in the image of $R_0$ exactly when its image in $K$ has valuation $\le 1$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi\in K_0$ with $0<v(\varpi.\varpi)<1$ in $K$ and such that every nonzero $a\in K_0$ satisfies $v(\varpi.\varpi)^N\le v(a)\le v(\varpi.\varpi)^{-N}$ for some $N$; let $\varpi_0\in R_0$ be irreducible with image $\varpi.\varpi$, and assume `hex`, that $\varpi$ is exhausting: every point of `upperHalfPlane K₀ K` lies in `affinoid ϖ n` for some $n$. Let $G$ be a group with a homomorphism $\rho : G\to \mathrm{PGL}(2,K_0)$ and an action of $G$ on the vertices [`LT.LatticeTree.Vertex R₀ K₀`](def/LatticeTreeOrbital.html#L349) (homothety classes of full lattices) which preserves adjacency in `BruhatTits.tree R₀ K₀` and which factors through $\rho$ in the sense that $g\cdot w=\rho(g)\cdot w$ for all $g,w$; assume the holomorphic ring `Omega.HolRingOf ϖ ρ` is a domain. Let $\Gamma\le G$ be such that every dart of the tree has finite stabiliser in $\Gamma.\mathrm{map}\,\rho$, the sets of $\Gamma$-orbits of vertices and of darts are finite, and `hexch`: some $\gamma\in\Gamma$ fails to preserve the vertex type relative to `stdVertex`. Write $\Gamma_+ := \Gamma\sqcap\mathrm{typePreserving}$, the intersection of $\Gamma$ with the subgroup of elements preserving the vertex type of every vertex relative to `stdVertex`, and let $\mathfrak M$ be `Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ₊`, the subfield of the fraction field of the holomorphic ring fixed by $\Gamma_+$. Assume `hvtf`: there is $\Gamma''\le\Gamma_+$ with $\Gamma''$ of nonzero relative index in $\Gamma_+$ and with $\rho(\Gamma'')$ torsion-free (every element of finite order is trivial); and `hnc`: $\mathfrak M$ contains an element outside the image of $K$. Then $\mathfrak M$ satisfies `IsCurveOver K`, i.e. it has principal divisors, each place of $\mathfrak M$ over $K$ has residue field finite over $K$, and $\Omega[\mathfrak M/K]$ is free of rank one over $\mathfrak M$; moreover $\mathfrak M$ is essentially of finite type over $K$; and there exists $x\in\mathfrak M$ transcendental over $K$ with $\mathfrak M$ finite-dimensional over $K(x)$.
--
--   This is the statement that the field of $\Gamma_+$-invariant meromorphic functions on Drinfeld's upper half plane is the function field of a curve over $K$ — the field-theoretic half of Mumford's analytic uniformisation, in the form used on the Čerednik–Drinfeld route. The two non-structural hypotheses (virtual torsion-freeness of $\rho(\Gamma_+)$ and existence of a non-constant invariant function) are left as assumptions here, to be supplied at the arithmetic instance; the result feeds the construction of the Shimura-curve models and the comparison of function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range

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

    (Γ : Subgroup G)
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge Γ (BruhatTits.tree R₀ K₀))]
    (hexch : ∃ γ : G, γ ∈ Γ ∧ γ ∉ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))

    (hvtf : ∃ Γ'' : Subgroup G, Γ'' ≤ Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ∧
      Γ''.relIndex (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) ≠ 0 ∧
      ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1)

    (hnc : ∃ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))),
      x ∉ Set.range (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))))) :
    IsCurveOver K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) ∧
    Algebra.EssFiniteType K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) ∧
    ∃ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))))) ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))) := by sorry
