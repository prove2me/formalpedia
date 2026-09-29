-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
-- name    : AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/62f95df8-96cc-541f-96e2-184ce616df79
-- title:
--   Period datum of a Mumford quotient pinned to analytic periods
-- statement:
--   Throughout, $C$ denotes the completion $A.\mathrm{valuation}.\mathrm{Completion}$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` at the valuation of a valuation subring $A$, and $\Omega =$ `Omega.upperHalfPlane K₀ C` denotes the complement in $C$ of the image of $K₀$, on which $PGL_2(K₀)$ acts by `Omega.pmoebius` (the fractional linear action on $\mathbb P^1(C) =$ `OnePoint C`, read back in $C$).
--
--   *Arithmetic data.* A prime $r$; a valuation subring $A$ of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime r`, i.e. $r$ lies in the nonunits of $A$; a group $S$ together with homomorphisms $\mathrm{scalar} : S \to D$ and $\iota : D \to S$, where $D = A.\mathrm{decompositionSubgroup}\ \mathbb Q$, such that $\mathrm{scalar}(\iota\tau) = \tau$ for all $\tau \in D$ (hypothesis `hι`), so that $S$ is a group over the decomposition group with a distinguished section.
--
--   *Local data.* A field $K₀$ with an algebra map to $C$; a discrete valuation domain $R₀$ with finite residue field, equipped with an algebra map to $K₀$ making $K₀$ its fraction field; the hypothesis `hR₀`, that $x \in K₀$ lies in the image of $R₀$ exactly when its image in $C$ has valuation $\le 1$; a pseudo-uniformiser $ϖ$ for $K₀$ in $C$, that is an element $ϖ.ϖ \in K₀$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that the valuation of every nonzero element of $K₀$ is squeezed between $v(ϖ.ϖ)^{N}$ and $v(ϖ.ϖ)^{-N}$ for some $N$; an irreducible $ϖ₀ \in R₀$ with $ϖ₀ \mapsto ϖ.ϖ$ (hypothesis `hϖ`); the hypothesis `hex`, that $ϖ$ is exhausted, i.e. every point of $\Omega$ lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr`, that the image of $ϖ.ϖ$ in $C$ has the same valuation as $r$.
--
--   *Group and tree data.* A group $G$ with a homomorphism $ρ : G \to PGL_2(K₀)$ such that the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on $\Omega$ (functions on $\Omega$ which on each affinoid are uniform limits, with uniformly bounded valuations, of pole-free rational functions) is a domain, and such that $PGL_2(K₀)$ acts on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` of homothety classes of full $R₀$-lattices in $K₀^2$ preserving adjacency. A subgroup $Γ \le G$ with `htp`: the image $Γ.\mathrm{map}\ ρ$ is contained in the type-preserving subgroup, the elements whose action preserves `Mumford.vertexType`, the parity of the distance from the standard vertex; the image acts on the tree as a graph action, and `hfin` asserts that the stabiliser in $Γ.\mathrm{map}\ ρ$ of every dart of the tree is finite.
--
--   *The quotient curve.* A field $FC$ with `IsCurveOver C FC` (principal divisors exist with degree zero, every place has residue field finite over $C$, and $\Omega^1_{FC/C}$ is free of rank one), an isomorphism $e_{FC}$ of $C$-algebras from $FC$ onto the subfield `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ` of $\mathrm{Frac}(\mathrm{HolRingOf}\ ϖ\ ρ)$ of elements fixed by every element of $Γ$, and `hfg`: there is a transcendental $x \in FC$ over $C$ with $FC$ finite over $C(x)$.
--
--   *Combinatorial data.* Finite types $E$ and $V$, a degeneracy datum $D$ on them (maps $a, b : E \to V$ and widths $w : E \to \mathbb N^{+}$), a bijection $e_V$ from the orbit quotient of the vertices of the tree under $Γ.\mathrm{map}\ ρ$ onto $V$, and a bijection $e_E$ from the set of those orbits of darts whose chosen representative has first endpoint of vertex type $0$ onto $E$. The hypotheses `hDa`, `hDb` state that for such a dart orbit $e$, $D.a(e_E e)$ and $D.b(e_E e)$ are the $e_V$-labels of the orbits of the first and second endpoints of the representative dart, and `hDw` that $D.w(e_E e)$ is the cardinality of the stabiliser of that dart in $Γ.\mathrm{map}\ ρ$.
--
--   *The homological dictionary.* A vertex $v₀$ and a homomorphism $Φ$ from $\mathrm{Additive}(\mathrm{Abelianization}(Γ.\mathrm{map}\ ρ))$ to the ribbon kernel $\mathrm{ribbonKernel}\ D$, the intersection inside $E \to \mathbb Z$ of the kernels of the pushforwards along $D.a$ and $D.b$, such that (hypothesis `hΦ`) for every $γ$ and every type-$0$ dart orbit $e$, the $e$-coordinate of $Φ(\bar γ)$ equals `Mumford.pathCycle`, the signed number of crossings of the orbit $e$ by the chosen path from $v₀$ to $γ \cdot v₀$.
--
--   *The uniformisation of places.* A map $pt$ from $\Omega$ to the places of $FC$ over $C$ (valuation subrings of $FC$, proper, containing the image of $C$ and principal ideal rings) with: `hpt_fib`, $pt\,z = pt\,z'$ if and only if $z' = γ \cdot z$ for some $γ \in Γ.\mathrm{map}\ ρ$; `hpt_onto`, $pt$ is surjective; and `hpt`, a conjunction of two clauses: for every $z \in \Omega$ and $x \in FC$, $x$ lies in the valuation subring of $pt\,z$ precisely when $e_{FC}(x)$ is represented in $\mathrm{Frac}(\mathrm{HolRingOf}\ ϖ\ ρ)$ as $g/h$ with $h$ a non-zero-divisor whose underlying holomorphic function does not vanish at $z$; and for every $z$ and every such invariant fraction $g/h$ with $h(z) \ne 0$, the evaluation at the place $pt\,z$ of the corresponding element of $FC$ is $g(z)/h(z)$, and that element lies in the nonunits of the valuation subring of $pt\,z$ if and only if $g(z) = 0$.
--
--   *Semilinear Galois data.* A homomorphism $\mathrm{galFC}$ from $S$ to the group `SemilinearAut C FC` of pairs of ring automorphisms of $FC$ and of $C$ compatible with the algebra map, with `hgalFC_base` asserting that the base component of $\mathrm{galFC}(σ)$ acts on $C$ as $\mathrm{scalar}(σ)$; and `hgal`, asserting that every $σ \in S$ is realised by a pair $(n, t)$ with $n \in G$ in the normaliser of $Γ$ and $t$ an isometric automorphism of $C$ over $K₀$, in the sense that the action of $\mathrm{galFC}(σ)$ on $FC$ corresponds under $e_{FC}$, on the fraction field, to the action of $n$ composed with the map induced by $t$ on coefficients.
--
--   *Compatibility of the Galois action with the combinatorics.* Homomorphisms $π_V : S \to \mathrm{Perm}\,V$, $π_E : S \to \mathrm{Perm}\,E$ and $\mathrm{sgn} : S \to \mathbb Z^{\times}$, subject to: `hπV`, for every $σ$ and every realising pair $(n,t)$ as in `hgal`, the permutation $π_V(σ)$ sends the $e_V$-label of the orbit of a vertex $v$ to that of the orbit of $ρ(n) \cdot v$; `hπE`, for every $σ$, every realising pair $(n,t)$ and every type-$0$ dart orbit $e$, if $ρ(n)$ is type-preserving then $\mathrm{sgn}(σ) = 1$ and $e_E^{-1}(π_E(σ)(e_E e))$ is the orbit of $ρ(n) \cdot e$, while if $ρ(n)$ is not type-preserving then $\mathrm{sgn}(σ) = -1$ and $e_E^{-1}(π_E(σ)(e_E e))$ is the orbit of the reversal of $ρ(n)\cdot e$; `hπ_width`, the widths $D.w$ are invariant under $π_E$; `hsgn_pos` and `hsgn_neg`, that $π_E$ is compatible with $D.a, D.b$ and $π_V$, preserving the two ends when $\mathrm{sgn}(σ) = 1$ and interchanging them when $\mathrm{sgn}(σ) = -1$; `hπ_inertia`, that for $τ$ in the decomposition subgroup whose underlying automorphism lies in `A.inertiaSubgroupIn ℚ` one has $π_V(\iota τ) = 1$, $π_E(\iota τ) = 1$ and $\mathrm{sgn}(\iota τ) = 1$; and finally a homomorphism $\mathrm{actZ}$ from $S$ to the $\mathbb Z$-linear automorphisms of $\mathrm{ribbonKernel}\ D$ with `hactZ`: $(\mathrm{actZ}(σ)x)(π_E(σ)e) = \mathrm{sgn}(σ)\, x(e)$ for all $x$ and $e$.
--
--   *Conclusion.* Under these hypotheses there exist an intermediate field $K$ of $\mathbb Q \subseteq C$ and an additive homomorphism $\mathrm{ord} : \mathrm{Additive}(K^{\times}) \to \mathbb Z$ such that the following four assertions hold.
--
--   First, for every $k \in K^{\times}$ the valuation of $k$ in $C$ equals $v(r)^{\mathrm{ord}(k)}$, so that $\mathrm{ord}$ reads valuations of elements of $K$ in powers of the valuation of $r$.
--
--   Second, for every $σ$ in the decomposition subgroup of $A$ over $\mathbb Q$ whose underlying $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lies in `A.inertiaSubgroupIn ℚ`, and for every $\mathbb Q$-algebra automorphism $s$ of $C$ implementing the action of $σ$ (that is, $s\,c = σ \cdot c$ for all $c \in C$), $s$ fixes every element of $K$.
--
--   Third, for every $n > 0$ with $r \nmid n$ and every $k \in K^{\times}$ with $\mathrm{ord}(k) = 0$ there is $k' \in K^{\times}$ with $k'^{\,n} = k$.
--
--   Fourth, there exists a period datum $P : \mathrm{PeriodDatum}\ D\ K\ C\ \mathrm{ord}$, that is a symmetric $\mathbb Z$-bilinear pairing $P.Q$ on $\mathrm{ribbonKernel}\ D$ with values in $\mathrm{Additive}(K^{\times})$ whose $\mathrm{ord}$ is the ribbon Gram form $\mathrm{ribbonGram}\ D$ (the width-weighted pairing restricted to the ribbon kernel), such that for all $x, y \in C$ lying in $\Omega$ with $\mathrm{pmoebius}(γ)x \ne y$ for every $γ \in Γ.\mathrm{map}\ ρ$, and for all $α, β \in Γ.\mathrm{map}\ ρ$,
--   $$P.Q\bigl(Φ(\bar α), Φ(\bar β)\bigr) \cdot \mathrm{period}\bigl((Γ.\mathrm{map}\ ρ).\mathrm{subtype}\bigr)\,x\,y\,α\,β \; = \; 1$$
--   in $C$, the first factor being taken multiplicatively in $K^{\times}$ and then mapped into $C$, and the second being the theta period `Omega.period` for the inclusion of $Γ.\mathrm{map}\ ρ$ into $PGL_2(K₀)$ with base points $x$ and $y$, namely the value at $\mathrm{pmoebius}(β)y$ of the theta product with divisor arguments $x$ and $\mathrm{pmoebius}(α)x$ and base point $y$. Thus the algebraic period pairing of $P$, read through the dictionary $Φ$ between the abelianisation of $Γ.\mathrm{map}\ ρ$ and the ribbon kernel, is inverse to the analytic Manin–Drinfeld period, independently of the admissible pair of base points.
--
--   This is the period module of the Čerednik–Drinfeld uniformisation package: it produces the period field $K$ inside the completion $C$, its order map, and a period datum on the degeneracy datum $D$ of the quotient graph whose pairing inverts the analytically defined theta periods of the Schottky-type group $Γ.\mathrm{map}\ ρ$. It is used in the assembly of the equivariant Mumford uniformisation of the Jacobian of the quotient curve, [`AlgebraicCurve.Pic0.exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.lean

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

theorem AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient

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
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∃ (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ),
      (∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
          ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)) ∧
      (∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k) ∧
      ∃ P : PeriodDatum D (↥K) A.valuation.Completion ord,
        ∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
          ∀ α β : ↥(Γ.map ρ),
            ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
                (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1 := by sorry
