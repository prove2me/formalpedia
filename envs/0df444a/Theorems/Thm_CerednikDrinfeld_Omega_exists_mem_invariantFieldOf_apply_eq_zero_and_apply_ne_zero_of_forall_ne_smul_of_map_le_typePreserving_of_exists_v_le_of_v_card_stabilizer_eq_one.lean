-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
-- name    : CerednikDrinfeld.Omega.exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/7f8ea231-1e69-5e3e-a77d-555b7f7724d6
-- title:
--   Invariant meromorphic functions separating two distinct ρ(Γ)-orbits
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume: (`hrk`) for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb{N}$ with $v(x)^n\le v(y)$; (`hval`) for every $\varepsilon\neq 0$ in $\Gamma_0$ there is $y\neq 0$ in $K$ with $v(y)\le\varepsilon$; and that $K$ is complete and algebraically closed. Let $R_0$ be a discrete valuation domain with fraction field $K_0$ and finite residue field such that an element of $K_0$ lies in the image of $R_0$ precisely when its image in $K$ has valuation $\le 1$. Let $\varpi$ be a pseudo-uniformizer, i.e. an element $\varpi.\varpi\in K_0$ whose image in $K$ has $0<v<1$ and such that every nonzero $a\in K_0$ satisfies $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$ for some $N$, and let $\varpi_0\in R_0$ be irreducible with image $\varpi.\varpi$; assume `hex`, that every point of the Drinfeld upper half plane $\Omega=K\setminus\mathrm{im}(K_0\to K)$ lies in some affinoid $\mathrm{affinoid}\,\varpi\,n$. Let $G$ be a group and $\rho\colon G\to \mathrm{PGL}_2(K_0)$ a homomorphism such that the ring $\mathrm{HolRingOf}\,\varpi\,\rho$ — the ring `Omega.holRing ϖ` of functions $\Omega\to K$ holomorphic on each affinoid — is a domain. Let $\Gamma\le G$ be a subgroup whose image $\Delta=\rho(\Gamma)$ preserves the vertex type on the Bruhat–Tits tree of $R_0$ relative to the standard vertex, acts on that tree by graph automorphisms, has finite dart stabilisers, has $v$ of the cardinality of every vertex stabiliser equal to $1$ in $K$, and has finitely many vertex orbits and finitely many dart orbits. Then for all $z,z'\in\Omega$ lying in different $\Delta$-orbits, that is $z'\neq\gamma\cdot z$ for every $\gamma\in\Delta$, there exist $g,h$ in the holomorphic ring with $h$ a non-zero-divisor such that the fraction $g/h$ in the fraction field lies in the subfield `Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ` attached to $\Gamma$, and $h(z)\neq0$, $h(z')\neq0$, $g(z)=0$, $g(z')\neq0$.
--
--   This is the separation (injectivity) half of the identification of points of the Mumford quotient of $\Omega$ by $\Delta=\rho(\Gamma)$ with places of the field of $\Gamma$-invariant meromorphic functions: an invariant function regular at both points which vanishes at $z$ but not at $z'$. It is used in the comparison of places of the invariant field with $\Delta$-orbits, and thence in the statements about images of points under the Čerednik–Drinfeld frame maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one

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
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))] :
    ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), (∀ γ : ↥(Γ.map ρ), z' ≠ (γ : PGL(2, K₀)) • z) →
      ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
        Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ ∧
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 ∧
        (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 ∧ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by sorry
