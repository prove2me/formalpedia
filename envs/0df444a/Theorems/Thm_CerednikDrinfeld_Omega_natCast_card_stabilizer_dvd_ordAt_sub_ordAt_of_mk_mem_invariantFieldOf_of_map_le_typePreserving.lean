-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving
-- name    : CerednikDrinfeld.Omega.natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/bc20e1e4-67b8-5953-b994-0939a2f64f75
-- title:
--   Stabiliser order divides vanishing orders of Γ-invariant functions
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two hypotheses: for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$, and every nonzero $\varepsilon\in\Gamma_0$ dominates $v(y)$ for some $y\neq 0$; assume moreover $K$ complete and algebraically closed. Let $R_0$ be a discrete valuation domain with finite residue field, with fraction field $K_0$, such that an element of $K_0$ comes from $R_0$ exactly when its image in $K$ has valuation $\le 1$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi\in K_0$ whose image in $K$ has valuation strictly between $0$ and $1$ and such that every nonzero $a\in K_0$ satisfies $v(\varpi.\varpi)^N\le v(a)\le v(\varpi.\varpi)^{-N}$ for some $N$; let $\varpi_0\in R_0$ be irreducible with image $\varpi.\varpi$, and assume $\varpi$ is exhausted, i.e. every point of the Drinfeld upper half plane $\Omega=K\setminus K_0$ lies in some affinoid $\mathrm{affinoid}\ \varpi\ n$. Let $G$ be a group with a homomorphism $\rho\colon G\to \mathrm{PGL}(2,K_0)$ such that the ring $\mathcal O(\Omega)$ of functions $\Omega\to K$ holomorphic on each affinoid (written `HolRingOf` $\varpi\ \rho$) is a domain. Let $\Gamma\le G$ be a subgroup whose image $\rho(\Gamma)$ is type-preserving, i.e. preserves the vertex type relative to the standard vertex of the Bruhat–Tits tree of $R_0$ in $K_0$, acts on that tree by graph automorphisms, has finite stabilisers of all darts, and has finitely many orbits of vertices and of darts. Let $z\in\Omega$ and assume the cardinality $e=\#\mathrm{Stab}_{\rho(\Gamma)}(z)$ is nonzero in $K$ (in particular the stabiliser is finite and $e$ is invertible in $K$: the tame case). Finally let $g,h\in\mathcal O(\Omega)$ with $g\neq0$, $h$ a non-zero-divisor, and suppose the fraction $g/h$ in the fraction field lies in the subfield of $\Gamma$-invariants `Mumford.invariantFieldOf`. Then, as integers, $e$ divides $\mathrm{ord}_z(g)-\mathrm{ord}_z(h)$, where $\mathrm{ord}_z(F)$ is the supremum of the $n$ with $(\text{coordSub}\ \varpi\ z)^n\mid F$.
--
--   This is the local integrality statement behind the divisor theory of Mumford curves: at a point of the Drinfeld upper half plane the order of vanishing of a $\Gamma$-invariant meromorphic function is a multiple of the order of the stabiliser of the point in the image group, in the case where that order is invertible in $K$. It feeds the comparison of orders at a place of the invariant field with orders at $z$ used in the Čerednik–Drinfeld description of the quotient curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (z : ↥(Omega.upperHalfPlane K₀ K))
    (htame : ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℕ) : K) ≠ 0)
    (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ) :
    ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℤ) ∣
      (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)) := by sorry
