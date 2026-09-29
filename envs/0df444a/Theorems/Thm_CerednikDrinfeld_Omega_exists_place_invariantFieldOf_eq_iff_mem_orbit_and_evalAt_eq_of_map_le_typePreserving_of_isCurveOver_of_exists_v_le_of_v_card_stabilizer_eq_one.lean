-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_eq_iff_mem_orbit_and_evalAt_eq_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le_of_v_card_stabilizer_eq_one
-- name    : CerednikDrinfeld.Omega.exists_place_invariantFieldOf_eq_iff_mem_orbit_and_evalAt_eq_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3db690ab-9f43-5bb4-af27-1b2313ec5ed8
-- title:
--   Points of the Mumford curve: orbits, surjectivity, evaluation
-- statement:
--   Let $K_0\subseteq K$ be fields with $K$ valued in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed, and assume the rank-one condition `hrk` (for $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n$ with $v(x)^n\le v(y)$) together with `hval` (every nonzero $\varepsilon\in\Gamma_0$ dominates $v(y)$ for some $y\neq 0$). Let $R_0$ be a discrete valuation ring with fraction field $K_0$ and finite residue field such that $R_0$ is exactly the set of $x\in K_0$ with $v(x)\le 1$, let $\varpi$ be a pseudo-uniformiser (an element of $K_0$ with $0<v(\varpi)<1$ satisfying the scaling condition) which is the image of an irreducible $\varpi_0\in R_0$ and whose affinoids exhaust the Drinfeld upper half plane $\Omega=K\setminus K_0$, so that every point of $\Omega$ lies in some affinoid. Let $G$ be a group acting through $\rho:G\to \mathrm{PGL}(2,K_0)$, assume the ring $\mathcal{O}(\Omega)=$ `HolRingOf` of functions $\Omega\to K$ that are holomorphic on each affinoid (uniform limits of pole-free rational functions, uniformly bounded) is a domain, and let $\Gamma\le G$ have image $\rho(\Gamma)$ contained in the type-preserving subgroup, i.e. preserving the parity of the distance to the standard vertex in the Bruhat–Tits tree of homothety classes of full $R_0$-lattices in $K_0^2$, acting on that tree by graph automorphisms, with finite dart stabilisers, with finitely many orbits of vertices and of darts, and tame vertex stabilisers in the sense that $v$ of the image in $K$ of the cardinality of each vertex stabiliser equals $1$. Let $FC$ be a field over $K$ with a $K$-algebra isomorphism $eFC$ onto the subfield $\mathfrak{M}$ of $\mathrm{Frac}(\mathcal{O}(\Omega))$ of elements fixed by every $\gamma\in\Gamma$, with $FC$ a curve over $K$ (principal divisors of degree zero, finite residue extensions at all places, $\Omega_{FC/K}$ free of rank one) and essentially of finite type over $K$, and suppose some element of $FC$ is not in $K$. Then there is a map $\mathrm{pt}$ from $\Omega$ to the places of $FC$ over $K$ (valuation subrings containing $K$, proper, principal ideal rings) such that: $\mathrm{pt}(z)=\mathrm{pt}(z')$ if and only if $z'=\gamma\cdot z$ for some $\gamma\in\rho(\Gamma)$; $\mathrm{pt}$ is surjective; $x\in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ exactly when $eFC(x)$ is the class of a fraction $g/h$ with $g,h\in\mathcal{O}(\Omega)$, $h$ a nonzerodivisor and $h(z)\neq 0$; and for all such $g,h$ whose fraction lies in $\mathfrak{M}$ and with $h(z)\neq 0$, the value of the corresponding element of $FC$ at $\mathrm{pt}(z)$ is $g(z)/h(z)$, and that element lies in the maximal ideal (the nonunits of the valuation subring) if and only if $g(z)=0$.
--
--   This is the uniformisation statement for Mumford curves in the form needed downstream: the $K$-points of the curve with function field $\mathfrak{M}=\mathrm{Frac}(\mathcal{O}(\Omega))^{\Gamma}$ are precisely the $\rho(\Gamma)$-orbits of Drinfeld's upper half plane, and functions are evaluated at a point by evaluating representing holomorphic fractions. It is the edition carrying the per-vertex tameness hypothesis, and it feeds the construction of an equivariant family of uniformisations used in the degree-zero Picard group of the Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_eq_iff_mem_orbit_and_evalAt_eq_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le_of_v_card_stabilizer_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_place_invariantFieldOf_eq_iff_mem_orbit_and_evalAt_eq_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le_of_v_card_stabilizer_eq_one

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

    (FC : Type) [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ))

    [IsCurveOver K FC] [Algebra.EssFiniteType K FC]

    (hnc : ∃ x : FC, x ∉ Set.range (algebraMap K FC)) :
    ∃ pt : ↥(Omega.upperHalfPlane K₀ K) → Place K FC,

      (∀ z z' : ↥(Omega.upperHalfPlane K₀ K),
        pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z) ∧

      Function.Surjective pt ∧

      ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))) := by sorry
