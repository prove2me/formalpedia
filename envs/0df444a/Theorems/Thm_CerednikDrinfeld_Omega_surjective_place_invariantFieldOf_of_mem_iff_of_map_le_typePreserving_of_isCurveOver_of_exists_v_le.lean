-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le
-- name    : CerednikDrinfeld.Omega.surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/72b0bd24-9221-5709-97ea-0cc71b5e3e01
-- title:
--   Every place of the invariant field comes from Ω
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to the rank-one condition that for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$ (`hrk`), and to the condition that every nonzero $\varepsilon\in\Gamma_0$ dominates the value of some nonzero element of $K$ (`hval`); assume $K$ complete and algebraically closed. Let $R_0$ be a discrete valuation domain with fraction field $K_0$ and finite residue field, such that the image of $R_0$ in $K_0$ consists exactly of the $x$ with $v(x)\le 1$ in $K$ (`hR₀`). Let $\varpi$ be a pseudo-uniformizer (an element $\varpi.\varpi\in K_0$ with $0<v(\varpi.\varpi)<1$ whose powers scale all nonzero values of $K_0$), coming from an irreducible $\varpi_0\in R_0$, and exhausted: every point of the Drinfeld upper half-plane $\Omega=K\setminus\mathrm{im}(K_0\to K)$ lies in some affinoid $\mathrm{affinoid}\,\varpi\,n$. Let $G$ be a group, $\rho:G\to \mathrm{PGL}(2,K_0)$, and assume the holomorphic ring $\mathrm{HolRingOf}\,\varpi\,\rho$ — the ring $\mathrm{holRing}\,\varpi$ of functions $\Omega\to K$ that on each affinoid are uniform limits of uniformly bounded pole-free rational functions — is a domain. Let $\Gamma\le G$ be a subgroup whose image $\rho(\Gamma)$ is type-preserving on the Bruhat–Tits tree of $R_0,K_0$ (it preserves the parity of the distance to the standard vertex), acts on that tree by graph automorphisms, has finite dart stabilisers, and has finite vertex and dart quotients. Let $FC$ be a field extension of $K$ together with a $K$-algebra isomorphism $e_{FC}$ onto the subfield $\mathrm{invariantFieldOf}\,K\,G\,(\mathrm{HolRingOf}\,\varpi\,\rho)\,\Gamma$ of $\Gamma$-invariants inside the fraction field of the holomorphic ring, and assume $FC$ is a curve over $K$ (principal divisors of degree zero exist, all residue fields of places are finite over $K$, and $\Omega[FC/K]$ is free of rank one) and essentially of finite type over $K$. Finally let $\mathrm{pt}:\Omega\to \mathrm{Place}\,K\,FC$ be a map such that for every $z\in\Omega$: an element $x\in FC$ lies in the valuation subring of $\mathrm{pt}\,z$ precisely when $e_{FC}(x)$ can be written as $\mathrm{Localization.mk}\ g\ h$ with $g,h$ in the holomorphic ring, $h$ a non-zero-divisor and $h(z)\neq 0$; and for all such $g,h$ with $\mathrm{Localization.mk}\ g\ h$ invariant and $h(z)\neq 0$, the evaluation of $\mathrm{pt}\,z$ at the corresponding element of $FC$ is $g(z)/h(z)$, and that element is a non-unit of the valuation subring iff $g(z)=0$. Then $\mathrm{pt}$ is surjective: every place of $FC$ over $K$ is $\mathrm{pt}\,z$ for some $z\in\Omega$.
--
--   This is the properness (completeness) half of the identification of the Mumford quotient as a curve: combined with the local description of the places of the invariant field, it says that the analytic points of $\Omega$ exhaust all places of that field over $K$. It feeds the statement that $\mathrm{pt}\,z=\mathrm{pt}\,z'$ exactly when $z,z'$ lie in the same $\Gamma$-orbit, and the comparison of the function field of the Čerednik–Drinfel'd quotient with the field of $\Gamma$-invariant meromorphic functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le.lean

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
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le

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

    (FC : Type) [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ))

    [IsCurveOver K FC] [Algebra.EssFiniteType K FC]
    (pt : ↥(Omega.upperHalfPlane K₀ K) → Place K FC)
    (hpt : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0)))) :
    Function.Surjective pt := by sorry
