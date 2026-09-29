-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/11ecb968-c0eb-5c17-a09f-977b44166581
-- title:
--   Theta uniformisation of Pic⁰ of a tame Mumford quotient
-- statement:
--   Throughout, $C := A.valuation.Completion$ denotes the completion of the algebraic closure of $\mathbb Q$ at the valuation subring $A$, and $\Omega :=$ `Omega.upperHalfPlane K₀ C` is the complement in $C$ of the image of $K_0$, Drinfeld's upper half plane over the local constants $K_0$.
--
--   **Arithmetic base.** A prime $r$; a valuation subring $A$ of `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime r`, i.e. $r$ lies in the nonunits of $A$; a group $S$ together with a homomorphism `scalar : S →* A.decompositionSubgroup ℚ` and a homomorphism `ι` in the opposite direction with `hι : scalar (ι τ) = τ` for every $\tau$ in the decomposition group.
--
--   **Local constants.** A field $K_0$ with a $K_0$-algebra structure on $C$; a discrete valuation ring $R_0$ with fraction field $K_0$ and finite residue field; the hypothesis `hR₀`, that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation at most $1$; a pseudo-uniformizer $\varpi$, that is an element $\varpi \in K_0$ whose image in $C$ has valuation in $(0,1)$ and such that every nonzero element of $K_0$ is squeezed between a power of $v(\varpi)$ and the corresponding inverse power; an irreducible $\varpi_0 \in R_0$ with `hϖ₀`, `hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ`; the hypothesis `hex`, that $\varpi$ is exhausted, i.e. every point of $\Omega$ lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr`, that $v(\varpi) = v(r)$ in $C$.
--
--   **Group, level and tree.** A group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$, the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on $\Omega$ (functions holomorphic on every affinoid) being a domain, together with the graph actions of $\mathrm{PGL}_2(K_0)$ on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` of homothety classes of full $R_0$-lattices in $K_0^2$ and a decidability assumption for membership in the type-preserving subgroup. A subgroup $\Gamma \le G$ with `htp`, that $\rho(\Gamma)$ is contained in `Mumford.typePreserving`, the subgroup of elements preserving the parity `vertexType` of the distance to the standard vertex; a graph action of $\rho(\Gamma)$ on the tree; `hfin`, that every dart stabiliser in $\rho(\Gamma)$ is finite; and the tameness hypothesis `htame`, that for every vertex $w$ the cardinality of the stabiliser of $w$ in $\rho(\Gamma)$ has valuation $1$ in $C$.
--
--   **The curve.** A field $FC$ that is a $C$-algebra with `IsCurveOver C FC` (principal divisors exist, each place has residue field finite over $C$, and $\Omega^1_{FC/C}$ is free of rank one); a $C$-algebra isomorphism `eFC` from $FC$ onto the $\Gamma$-invariant subfield `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ` of the fraction field of the holomorphic ring; and `hfg`, the existence of a transcendental $x \in FC$ with $FC$ finite over $C(x)$.
--
--   **Combinatorial presentation of the quotient graph.** Finite types $E$, $V$ and a degeneracy datum $D$ on them, consisting of maps $a, b : E \to V$ and widths $w : E \to \mathbb Z_{>0}$; a bijection `eV` from the set of $\rho(\Gamma)$-orbits of vertices onto $V$; a bijection `eE` from the set of those $\rho(\Gamma)$-orbits of darts whose chosen representative has first vertex of type $0$ onto $E$; the compatibilities `hDa`, `hDb` identifying $D.a$ and $D.b$ of an edge with the orbits of the first and second vertex of the representing dart, and `hDw` identifying the width with the cardinality of the stabiliser of that dart. A base vertex $v_0$; an additive map $\Phi$ from `Additive (Abelianization (Γ.map ρ))` to the ribbon kernel `ribbonKernel D` (the intersection of the kernels of the two pushforward maps $(E \to \mathbb Z) \to (V \to \mathbb Z)$ along $a$ and $b$); and `hΦ`, that for every $\gamma \in \rho(\Gamma)$ and every even-type edge orbit $e$ the $e$-coordinate of $\Phi(\bar\gamma)$ equals `Mumford.pathCycle` of $\gamma$ based at $v_0$, the signed number of times the geodesic from $v_0$ to $\gamma v_0$ traverses $e$.
--
--   **Point-to-place map.** A map `pt` from $\Omega$ to `Place C FC`, a place being a valuation subring of $FC$ that contains the image of $C$, is not all of $FC$ and is a principal ideal ring; `hpt_fib`, that $\mathrm{pt}(z) = \mathrm{pt}(z')$ holds exactly when $z' = \gamma \cdot z$ for some $\gamma \in \rho(\Gamma)$; `hpt_onto`, that `pt` is surjective; and `hpt`, a two-part analytic description of `pt`: first, $x \in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ if and only if there are holomorphic $g, h$ with $h$ a non-zero-divisor, $h(z) \neq 0$ and `eFC x` equal to $g/h$ in the fraction field; second, for $g$ and a non-zero-divisor $h$ such that $g/h$ lies in the invariant field and $h(z) \neq 0$, the evaluation `(pt z).evalAt` of the corresponding element of $FC$ equals $g(z)/h(z)$, and that element lies in the nonunits of the valuation subring of $\mathrm{pt}(z)$ if and only if $g(z) = 0$.
--
--   **Galois data (summarised here).** A homomorphism `galFC` from $S$ to the group `SemilinearAut C FC` of pairs of ring automorphisms of $FC$ and of $C$ compatible with the structure map, with `hgalFC_base` saying that the base automorphism of `galFC σ` acts on $C$ as `scalar σ`, and `hgal` saying that each $\sigma$ is realised, after transport along `eFC`, by the action of some $n$ in the normalizer of $\Gamma$ composed with the semilinear automorphism of the fraction field induced by an isometric automorphism $t$ of $C$ fixing $K_0$ pointwise. Homomorphisms `πV : S →* Equiv.Perm V`, `πE : S →* Equiv.Perm E` and `sgn : S →* ℤˣ` together with: `hπV`, that for any $n, t$ realising $\sigma$ as above, `πV σ` transports vertex orbits along the action of $\rho(n)$; `hπE`, that under the same circumstances `πE σ` transports even-type edge orbits along $\rho(n)$ with $\mathrm{sgn}(\sigma) = 1$ when $\rho(n)$ is type-preserving, and along $\rho(n)$ followed by reversal of the dart with $\mathrm{sgn}(\sigma) = -1$ otherwise; `hπ_width`, that `πE` preserves widths; `hsgn_pos` and `hsgn_neg`, that `πE` is compatible with $a$ and $b$ respectively unswitched or switched according to the sign; and `hπ_inertia`, that `πV`, `πE` and `sgn` are trivial on `ι τ` for $\tau$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`. Finally a homomorphism `actZ` from $S$ to the group of $\mathbb Z$-linear automorphisms of the ribbon kernel with `hactZ`, that $(\mathrm{actZ}\,\sigma)(x)$ has $\pi_E(\sigma)(e)$-coordinate $\mathrm{sgn}(\sigma)\cdot x(e)$.
--
--   **Period field.** An intermediate field $K$ between $\mathbb Q$ and $C$; an additive map `ord` from `Additive Kˣ` to $\mathbb Z$ with `hord`, that $v(k) = v(r)^{\mathrm{ord}(k)}$ for every $k \in K^\times$; `hinK`, that every element of $K$ is fixed by each $\mathbb Q$-automorphism of $C$ inducing the action of an element of the inertia subgroup; and `hhens`, that every $k \in K^\times$ with $\mathrm{ord}(k) = 0$ has an $n$-th root in $K^\times$ for every $n > 0$ prime to $r$.
--
--   **Period datum and docking.** A period datum $P$ of type `PeriodDatum D K C ord`, that is a symmetric $\mathbb Z$-bilinear form $Q$ on the ribbon kernel with values in `Additive Kˣ` whose composite with `ord` is the ribbon Gram form of $D$ (the width pairing restricted to the ribbon kernel). The docking hypothesis `hQ`: for all $x, y \in \Omega$ such that $y$ lies in no $\rho(\Gamma)$-translate of $x$, and all $\alpha, \beta \in \rho(\Gamma)$,
--   $$Q\bigl(\Phi(\bar\alpha), \Phi(\bar\beta)\bigr) \cdot \Theta(x, \alpha x; y)(\beta y) = 1$$
--   in $C$, where the first factor is the image in $C$ of the corresponding element of $K^\times$ and the second is `Omega.period` for the inclusion of $\rho(\Gamma)$ into $\mathrm{PGL}_2(K_0)$, namely the value at $\beta\cdot y$ of the theta product $\prod'_{\gamma} \mathrm{crossRatio}$ attached to the divisor $x - \alpha x$ with base point $y$.
--
--   **Conclusion.** There exists an additive homomorphism
--   $$e_{\mathrm{Full}} : P.\mathrm{TorusPoints} = \operatorname{Hom}_{\mathbb Z}\bigl(\mathrm{ribbonKernel}\,D,\ \mathrm{Additive}\ C^\times\bigr) \longrightarrow \operatorname{Pic}^0(C, FC)$$
--   into the quotient of the degree-zero divisors of $FC$ by the principal ones, such that:
--
--   1. $e_{\mathrm{Full}}$ is surjective;
--
--   2. for every $u$ in the torus points, $e_{\mathrm{Full}}(u) = 0$ if and only if $u$ lies in `P.periodLattice`, the range of the $\mathbb Z$-linear map `P.QL` attached to $Q$;
--
--   3. (pinning on theta characters) for all $a, b, z_0 \in C$ lying in $\Omega$ such that no $\rho(\Gamma)$-translate of $a$ equals $z_0$ and no $\rho(\Gamma)$-translate of $b$ equals $z_0$, for every homomorphism $c : \rho(\Gamma) \to C^\times$ satisfying $c(\beta) = \Theta(a, b; z_0)(\beta z_0)$ for all $\beta \in \rho(\Gamma)$, for every torus point $u$ satisfying $u(\Phi(\bar\gamma)) = c(\gamma)$ for all $\gamma \in \rho(\Gamma)$, and for every degree-zero divisor $D_v$ whose underlying divisor is $[\mathrm{pt}(a)] - [\mathrm{pt}(b)]$, one has $e_{\mathrm{Full}}(u) = \mathrm{Pic}^0.\mathrm{mk}\,D_v$.
--
--   This is the torus-points half of the analytic uniformisation $0 \to \Lambda \to \operatorname{Hom}(Z, C^\times) \to \operatorname{Jac} \to 0$ of the Jacobian of a Mumford curve, in the form appropriate to a Drinfeld upper half plane quotient by a level $\Gamma$ with torsion but tame vertex stabilisers, and stated for an arbitrary period datum satisfying the docking identity rather than for a fixed choice of periods. It is used in the construction of the Galois-equivariant uniformisation of $\operatorname{Pic}^0$ of the Mumford quotient, the step that feeds the Čerednik–Drinfeld description of the reduction of a Shimura curve into the rest of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups
open CerednikDrinfeld AlgebraicCurve ModularCurve
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (hord : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k)))
    (hinK : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion))
    (hhens : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (hQ : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1)) :
    ∃ eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC,
      Function.Surjective eFull ∧ (∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice) ∧
      (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          eFull u = Pic0.mk Dv) := by sorry
