-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/2982d9b4-ca0b-5728-a3a7-bf1d7e586a29
-- title:
--   Equal theta multipliers give a principal divisor on a Mumford quotient
-- statement:
--   Throughout, write $K$ for the completion `A.valuation.Completion` of $\overline{\mathbb{Q}}$ at a valuation subring $A$ of `AlgebraicClosure ℚ`, where $A$ lies over the prime $r$ in the sense of `LiesOverPrime`, i.e. $r$ is a non-unit of $A$.
--
--   *Galois frame.* A group $S$ is given together with a homomorphism `scalar` to the decomposition subgroup of $A$ over $\mathbb{Q}$ and a homomorphism $\iota$ in the opposite direction which is a section of `scalar` (hypothesis `hι`: $\mathrm{scalar}(\iota\tau)=\tau$ for every $\tau$).
--
--   *Local frame.* A field $K_0$ with an algebra structure on $K$ over it is given, together with a discrete valuation ring $R_0$ which is a domain with fraction field $K_0$ and finite residue field, such that (`hR₀`) an element of $K_0$ lies in the image of $R_0$ precisely when its image in $K$ has valuation at most $1$. Furthermore $\varpi$ is a pseudo-uniformizer of $K_0$ relative to $K$, that is an element $\varpi.\varpi \in K_0$ whose image in $K$ has valuation strictly between $0$ and $1$ and such that the valuation of every non-zero element of $K_0$ is squeezed between a power of $v(\varpi.\varpi)$ and the inverse of that power; $\varpi_0 \in R_0$ is irreducible and maps to $\varpi.\varpi$ (`hϖ₀`, `hϖ`); the hypothesis `hex` states that $\varpi$ is exhausted, i.e. every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ lies in one of the affinoids `affinoid ϖ n`; and `hϖr` states $v(\varpi.\varpi) = v(r)$ in $K$.
--
--   *The level.* A group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ is given, the ring `Omega.HolRingOf ϖ ρ` of functions on $\Omega$ holomorphic on every affinoid being a domain, and $\mathrm{PGL}_2(K_0)$ acting on the Bruhat–Tits tree of $R_0$, $K_0$ by graph automorphisms. For a subgroup $\Gamma \le G$ it is assumed (`htp`) that $\rho(\Gamma)$ lies in the type-preserving subgroup, i.e. each of its elements preserves the parity of the distance to the standard vertex; $\rho(\Gamma)$ acts on the tree by graph automorphisms; all dart stabilisers in $\rho(\Gamma)$ are finite (`hfin`); and the action is tame in the sense that (`htame`) for every vertex $w$ the image in $K$ of the cardinality of the stabiliser of $w$ in $\rho(\Gamma)$ has valuation $1$.
--
--   *The curve.* $FC$ is a field with a $K$-algebra structure, which is a curve over $K$ in the sense of `IsCurveOver`: principal divisors of non-zero elements exist and have degree zero, all residue fields of places are finite-dimensional over $K$, and $\Omega_{FC/K}$ is free of rank one. An isomorphism $e_{FC}$ of $K$-algebras identifies $FC$ with the subfield of $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$ of elements fixed by every element of $\Gamma$, and `hfg` asserts the existence of a transcendental $x \in FC$ with $FC$ finite over $K(x)$.
--
--   *Combinatorial data.* Finite types $E$, $V$ carry a degeneracy datum $D$ (source and target maps $a, b : E \to V$ and widths $w : E \to \mathbb{N}^{+}$); $e_V$ identifies the set of $\rho(\Gamma)$-orbits of vertices with $V$, and $e_E$ identifies the set of those $\rho(\Gamma)$-orbit classes of darts whose chosen representative has source of vertex type $0$ with $E$. The hypotheses `hDa`, `hDb`, `hDw` require, for every such edge class $e$, that $D.a(e_E e)$ and $D.b(e_E e)$ be the orbit classes of the source and the target of the representative dart, and that $D.w(e_E e)$ be the cardinality of the stabiliser of that dart in $\rho(\Gamma)$. A vertex $v_0$ is fixed, and $\Phi$ is an additive map from the additivisation of the abelianisation of $\rho(\Gamma)$ to the ribbon kernel of $D$ (the intersection of the kernels of the two pushforwards along $D.a$ and $D.b$) such that (`hΦ`) for every $\gamma \in \rho(\Gamma)$ and every edge class $e$ the value of $\Phi(\gamma)$ at $e_E e$ equals the path cycle `Mumford.pathCycle` of the geodesic from $v_0$ to $\gamma \cdot v_0$, computed with respect to the inclusion of type-$0$ edge classes into dart classes, evaluated at $e$.
--
--   *Points as places.* A map $\mathrm{pt}$ from $\Omega$ to the places of $FC$ over $K$ is given, whose fibres are exactly the $\rho(\Gamma)$-orbits (`hpt_fib`: $\mathrm{pt}\,z = \mathrm{pt}\,z'$ iff $z' = \gamma \cdot z$ for some $\gamma \in \rho(\Gamma)$) and which is surjective (`hpt_onto`). The hypothesis `hpt` has two conjuncts: first, for all $z \in \Omega$ and $x \in FC$, the element $x$ lies in the valuation subring of $\mathrm{pt}\,z$ if and only if there are $g, h$ in $\mathrm{HolRingOf}\,\varpi\,\rho$ with $h$ a non-zero-divisor, $h(z) \neq 0$, and $e_{FC}(x) = g/h$ in $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$; second, for all $z$ and all such $g$, $h$ with $g/h$ lying in the invariant field and $h(z) \neq 0$, the evaluation at $\mathrm{pt}\,z$ of the corresponding element of $FC$ equals $g(z)/h(z)$, and that element lies in the non-units of the valuation subring of $\mathrm{pt}\,z$ precisely when $g(z) = 0$.
--
--   *Descent data.* A homomorphism $\mathrm{galFC}$ from $S$ to the semilinear automorphisms of $FC$ over $K$ is given whose base automorphism is the action of $\mathrm{scalar}\,\sigma$ on $K$ (`hgalFC_base`), and each $\sigma \in S$ is realised (`hgal`) by an element $n$ of the normaliser of $\Gamma$ in $G$ together with an isometric automorphism $t$ of $K$ over $K_0$, in the sense that $e_{FC}$ transports $\mathrm{galFC}\,\sigma$ to $n$ composed with the automorphism of $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$ induced by `Omega.toAmbientOf ϖ ρ t`. Homomorphisms $\pi_V : S \to \mathrm{Perm}(V)$, $\pi_E : S \to \mathrm{Perm}(E)$ and $\mathrm{sgn} : S \to \mathbb{Z}^{\times}$ are given, together with the compatibilities (summarised here) `hπV` and `hπE`: whenever $\sigma$ is realised by $(n,t)$ as above, $\pi_V\sigma$ acts on vertex orbits as $\rho n$, and on edge classes $\pi_E\sigma$ acts as $\rho n$ with $\mathrm{sgn}\,\sigma = 1$ if $\rho n$ is type-preserving, and as $\rho n$ followed by reversal of the dart with $\mathrm{sgn}\,\sigma = -1$ otherwise. Further, $\pi_E$ preserves widths (`hπ_width`), $\pi_E$ is compatible with $D.a$, $D.b$ through $\pi_V$ when the sign is $+1$ (`hsgn_pos`) and interchanges them when the sign is $-1$ (`hsgn_neg`), and (`hπ_inertia`) for every $\tau$ in the decomposition subgroup whose underlying automorphism lies in `inertiaSubgroupIn`, one has $\pi_V(\iota\tau) = 1$, $\pi_E(\iota\tau) = 1$ and $\mathrm{sgn}(\iota\tau) = 1$. Finally $\mathrm{actZ}$ is a homomorphism from $S$ to the $\mathbb{Z}$-linear automorphisms of the ribbon kernel of $D$ satisfying (`hactZ`) $(\mathrm{actZ}\,\sigma\,x)(\pi_E\sigma\,e) = \mathrm{sgn}\,\sigma \cdot x(e)$ for all $\sigma$, $x$, $e$.
--
--   *Theta data.* Two finite families of points of $K$ are given: $a, b, z$ indexed by $\mathrm{Fin}\,n$ and $a', b', z'$ indexed by $\mathrm{Fin}\,m$, all lying in $\Omega$ (`ha`, `hb`, `hz`, `ha'`, `hb'`, `hz'`), with the base points off the relevant orbits: for all $i$ and all $\gamma \in \rho(\Gamma)$ one has $\gamma \cdot a_i \neq z_i$ and $\gamma \cdot b_i \neq z_i$ for the Möbius action `pmoebius` (`hza`, `hzb`), and likewise $\gamma \cdot a'_j \neq z'_j$, $\gamma \cdot b'_j \neq z'_j$ (`hza'`, `hzb'`). The multiplier hypothesis `hmult` requires that for every $\beta \in \rho(\Gamma)$
--   $$\prod_{i} \Theta(a_i, b_i; z_i)(\beta \cdot z_i) \;=\; \prod_{j} \Theta(a'_j, b'_j; z'_j)(\beta \cdot z'_j),$$
--   where $\Theta(a,b;z_0)(z) = \prod_{\gamma \in \rho(\Gamma)} (z, z_0; \gamma a, \gamma b)$ is `Omega.theta` formed with the inclusion of $\rho(\Gamma)$ into $\mathrm{PGL}_2(K_0)$.
--
--   *Conclusion.* The divisor
--   $$\sum_{i} \bigl( [\mathrm{pt}\,a_i] - [\mathrm{pt}\,b_i] \bigr) \;-\; \sum_{j} \bigl( [\mathrm{pt}\,a'_j] - [\mathrm{pt}\,b'_j] \bigr)$$
--   of $FC$ over $K$, formed from the indicator finitely supported functions of the indicated places, is principal: there exists a non-zero $f \in FC$ such that the coefficient of this divisor at every place $v$ of $FC$ over $K$ equals the order $v.\mathrm{ord}\,f$.
--
--   This is the divisor-theoretic output of the theta-function construction on a Mumford quotient of the Drinfeld upper half plane, in the tame case where the orders of the vertex stabilisers of $\rho(\Gamma)$ are units for the valuation of the ambient complete field: families of theta functions with equal automorphy multipliers produce a function on the quotient curve with prescribed zeros and poles at the images of the chosen points. It feeds the construction of the period lattice and the uniformization of the degree-zero divisor class group, being cited by [`AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one.lean

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
open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve
open CerednikDrinfeld.Omega

theorem AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one

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
    (n m : ℕ) (a b z : Fin n → A.valuation.Completion) (a' b' z' : Fin m → A.valuation.Completion)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (ha' : ∀ j, a' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb' : ∀ j, b' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz' : ∀ j, z' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hza : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i) (hzb : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (hza' : ∀ j (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a' j) ≠ z' j) (hzb' : ∀ j (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b' j) ≠ z' j)
    (hmult : ∀ β : ↥(Γ.map ρ),
      ∏ i, Omega.theta (Γ.map ρ).subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z i)) =
        ∏ j, Omega.theta (Γ.map ρ).subtype (a' j) (b' j) (z' j) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z' j))) :
    Divisor.IsPrincipal (K := A.valuation.Completion) (F := FC)
      (∑ i, (Finsupp.single (pt ⟨a i, ha i⟩) 1 - Finsupp.single (pt ⟨b i, hb i⟩) 1) -
        ∑ j, (Finsupp.single (pt ⟨a' j, ha' j⟩) 1 - Finsupp.single (pt ⟨b' j, hb' j⟩) 1) : Divisor A.valuation.Completion FC) := by sorry
