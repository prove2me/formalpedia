-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
-- name    : CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/29e66474-5939-5df7-a93a-6a2ad4f2d8c6
-- title:
--   Places of the invariant field at points of Ω
-- statement:
--   Let $K_0$ be a field and $K$ a complete, algebraically closed valued field extension of $K_0$ with value group $\Gamma_0$, whose valuation satisfies: $v(x)<1$ and $y\neq 0$ imply $v(x)^n\le v(y)$ for some $n$. Let $R_0$ be a discrete valuation ring with fraction field $K_0$ and finite residue field, such that the image of $R_0$ in $K_0$ consists exactly of the elements whose image in $K$ has valuation $\le 1$. Let $\varpi$ be a pseudo-uniformizer (an element of $K_0$ with $0<v<1$ and the stated scaling property), arising from an irreducible $\varpi_0\in R_0$, and assume $\varpi$ is exhausted: every point of $\Omega=K\setminus K_0$ lies in some affinoid $\mathrm{affinoid}\,\varpi\,n$. Let $\rho\colon G\to \mathrm{PGL}_2(K_0)$ be a group homomorphism with $\mathcal{O}=\mathrm{HolRingOf}\,\varpi\,\rho$ (the ring of functions $\Omega\to K$ holomorphic on each affinoid, i.e. uniform limits of uniformly bounded pole-free rational functions) a domain, and let $\Gamma\le G$ satisfy: $\rho(\Gamma)$ preserves the parity of the distance to the standard vertex in the Bruhat–Tits tree of $R_0$, acts on that tree by graph automorphisms, has finite dart stabilisers, and has finitely many orbits of vertices and of darts. Let $FC$ be a field with a $K$-algebra isomorphism $e$ onto the invariant field $\mathrm{invariantFieldOf}\,K\,G\,\mathcal{O}\,\Gamma$, the subfield of $\mathrm{Frac}(\mathcal{O})$ of elements fixed by every $\gamma\in\Gamma$, and assume $FC$ contains an element outside the image of $K$. Then there is a map $\mathrm{pt}$ from $\Omega$ to places of $FC$ over $K$ (valuation subrings containing $K$, proper, and principal ideal rings) such that, for every $z\in\Omega$: an $x\in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ precisely when $e(x)=g/h$ in $\mathrm{Frac}(\mathcal{O})$ for some $g\in\mathcal{O}$ and some non-zero-divisor $h\in\mathcal{O}$ with $h(z)\neq 0$; and whenever $g/h$ lies in the invariant field with $h$ a non-zero-divisor and $h(z)\neq 0$, the evaluation of $\mathrm{pt}(z)$ at $e^{-1}(g/h)$ equals $g(z)/h(z)$, and $e^{-1}(g/h)$ lies in the maximal ideal of $\mathrm{pt}(z)$ if and only if $g(z)=0$.
--
--   This is the point-to-place map for the Mumford quotient of Drinfeld's upper half plane: each $z\in\Omega$ determines a place of the $\Gamma$-invariant field, whose valuation ring consists of the invariant meromorphic functions regular at $z$, with residue given by evaluation. The invariant field is carried here by an abstract field $FC$ identified with it by a $K$-algebra isomorphism, which is the form in which later results bind their places; it feeds the comparison of places with $\Gamma$-orbits and the surjectivity statement for the ring homomorphism from the function field to the invariant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving.lean

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
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving

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
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]

    (FC : Type) [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ))
    (hnc : ∃ x : FC, x ∉ Set.range (algebraMap K FC)) :
    ∃ pt : ↥(Omega.upperHalfPlane K₀ K) → Place K FC,
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
