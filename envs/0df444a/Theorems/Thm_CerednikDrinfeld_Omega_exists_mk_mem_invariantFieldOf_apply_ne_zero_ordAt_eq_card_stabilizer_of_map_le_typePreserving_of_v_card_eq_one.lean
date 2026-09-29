-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
-- name    : CerednikDrinfeld.Omega.exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/77c2b94b-aa6a-5826-8d64-31e480ea60d1
-- title:
--   Invariant function vanishing to the stabiliser order at a point
-- statement:
--   Let $K_0$ be a field and $K$ a complete, algebraically closed extension field of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two hypotheses on the value group: for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb{N}$ with $v(x)^n\le v(y)$, and every nonzero $\varepsilon\in\Gamma_0$ dominates $v(y)$ for some $y\neq0$ in $K$. Let $R_0$ be a discrete valuation domain with fraction field $K_0$ and finite residue field, such that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $K$ has valuation $\le 1$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi\in K_0$ with $0<v<1$ whose powers scale every nonzero element of $K_0$ from both sides, coming from an irreducible $\varpi_0\in R_0$, and assume $\varpi$ is exhausted: every point of $\Omega:=K\setminus\operatorname{im}(K_0\to K)$ lies in some affinoid $\mathrm{affinoid}\,\varpi\,n$. Let $G$ be a group, $\rho:G\to \mathrm{PGL}_2(K_0)$ a homomorphism, and assume $\mathrm{HolRingOf}\,\varpi\,\rho$ — by definition the ring $\mathrm{holRing}\,\varpi$ of functions $\Omega\to K$ holomorphic on every affinoid — is a domain. Let $\Gamma\le G$ be such that every element of $\rho(\Gamma)$ preserves the vertex type relative to the standard vertex on the Bruhat–Tits tree of $R_0$ (the graph `BruhatTits.tree R₀ K₀` on homothety classes of lattices), with $\rho(\Gamma)$ acting by graph automorphisms, all dart stabilisers in $\rho(\Gamma)$ finite, all vertex stabiliser orders of valuation $1$ in $K$ (tameness), and both the set of vertex orbits and the set of dart orbits finite. Then for every $z\in\Omega$ there exist $g,h\in \mathrm{HolRingOf}\,\varpi\,\rho$ with $h$ a non-zero-divisor such that the fraction $g/h$ lies in the subfield $\mathrm{Mumford.invariantFieldOf}\,K\,G\,(\mathrm{HolRingOf}\,\varpi\,\rho)\,\Gamma$ of the fraction field, $h(z)\neq 0$, $g\neq 0$, and $\mathrm{ordAt}\,\varpi\,g\,z$ — the supremum of the $n$ with $(\mathrm{coordSub}\,\varpi\,z)^n\mid g$ — equals the cardinality of the stabiliser of $z$ in $\rho(\Gamma)$.
--
--   This is the existence statement behind the ramification of the quotient map $\Omega\to\Gamma\backslash\Omega$ at a point of the Drinfel'd upper half plane: the ramification index at $z$ is exactly the order of the stabiliser of $z$, and a function realising it may be taken globally, as a quotient of two rigid-holomorphic functions on $\Omega$ whose denominator does not vanish at $z$ and which is invariant for $\Gamma$. It feeds the computation of the valuation at the corresponding place of the invariant field in terms of the orders $\mathrm{ordAt}$ of numerator and denominator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one.lean

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
open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mk_mem_invariantFieldOf_apply_ne_zero_ordAt_eq_card_stabilizer_of_map_le_typePreserving_of_v_card_eq_one

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

    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ.map ρ)) w) : ℕ) : K) = 1)
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (z : ↥(Omega.upperHalfPlane K₀ K)) :
    ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ ∧
      (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ g ≠ 0 ∧
      Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z = Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) := by sorry
