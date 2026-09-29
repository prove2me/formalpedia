-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
-- name    : CerednikDrinfeld.Omega.place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/678d4a35-d1f3-5d05-a1b4-f32f606b6be5
-- title:
--   Fibres of the point-to-place map are ρ(Γ)-orbits
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two conditions on the value group: for all $x,y \in K$ with $v(x)<1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$ (`hrk`), and every nonzero $\varepsilon \in \Gamma_0$ is bounded below by the value of some nonzero element of $K$ (`hval`); assume $K$ complete and algebraically closed. Let $R_0$ be a discrete valuation ring with finite residue field, with fraction field $K_0$, such that the image of $R_0$ in $K_0$ consists exactly of those $x$ with $v(\mathrm{alg}(x)) \le 1$ (`hR₀`). Let $\varpi$ be a pseudo-uniformizer for the pair $(K_0,K)$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ whose powers bracket the value of every nonzero element of $K_0$ from both sides, let $\varpi_0 \in R_0$ be irreducible with image $\varpi$, and assume the exhaustion property that every point of the Drinfeld upper half-plane $\Omega = K \setminus K_0$ lies in one of the affinoids $\mathrm{affinoid}\,\varpi\,n$. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring $\mathcal{O}(\Omega)$ of functions $\Omega \to K$ holomorphic on every affinoid, viewed with its $G$-action, is a domain. Let $\Gamma \le G$ be a subgroup whose image $\rho(\Gamma)$ preserves the parity of the distance to the standard vertex in the Bruhat–Tits tree of homothety classes of full $R_0$-lattices in $K_0^2$ (`htp`), with finite dart stabilisers, with $v$ of the cardinality of each vertex stabiliser, read in $K$, equal to $1$ (the tameness hypothesis `htame`), and with finitely many vertex orbits and dart orbits. Let $FC$ be a field with a $K$-algebra isomorphism $e$ onto the subfield of $\mathrm{Frac}(\mathcal{O}(\Omega))$ of elements fixed by every element of $\Gamma$, and let $\mathrm{pt}$ assign to each $z \in \Omega$ a place of $FC$ over $K$ (a valuation subring containing $K$, not everything, and a principal ideal ring) such that: an element $x \in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ exactly when $e(x)$ can be written as $\mathrm{mk}\,g\,h$ with $g,h \in \mathcal{O}(\Omega)$, $h$ a non-zero-divisor and $h(z) \neq 0$; and for such a representation of an invariant fraction, the residue evaluation of $\mathrm{pt}(z)$ at it is $g(z)/h(z)$, and it lies in the maximal ideal exactly when $g(z)=0$. Then for all $z,z' \in \Omega$ one has $\mathrm{pt}(z) = \mathrm{pt}(z')$ if and only if $z' = \gamma \cdot z$ for some $\gamma \in \rho(\Gamma)$.
--
--   This is the injectivity-on-orbits statement for the map from the Drinfeld upper half-plane to the places of the field of $\Gamma$-invariant meromorphic functions: the fibres of $z \mapsto \mathrm{pt}(z)$ are precisely the orbits of the image group $\rho(\Gamma)$, which is what identifies the set of such places with the quotient $\Omega/\rho(\Gamma)$. It is used in the construction of the Mumford quotient curve and in the proof that the induced homomorphism onto the invariant field is surjective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one.lean

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

theorem CerednikDrinfeld.Omega.place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one

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
    (∀ z z' : ↥(Omega.upperHalfPlane K₀ K),
        pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z) := by sorry
