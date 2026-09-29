-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8c1a1e99-fe54-5ede-90c8-45e25b039c61
-- title:
--   Equivariant Manin–Drinfeld uniformisation of Jacobians of Mumford quotients
-- statement:
--   Throughout, $r$ is a prime, $A$ is a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime r`, i.e. $r$ lies in the nonunits of $A$, and $C$ denotes the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ at $A$. A group $S$ is equipped with a homomorphism `scalar : S →* A.decompositionSubgroup ℚ` and a homomorphism $\iota$ in the other direction which is a section of `scalar` (`hι`).
--
--   **Constants and uniformiser.** $K_0$ is a field with an algebra structure to $C$, and $R_0$ is a discrete valuation domain with fraction field $K_0$ and finite residue field; `hR₀` says that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation $\le 1$. Further data: a pseudo-uniformiser $\varpi$ for $K_0$ in $C$ (an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$, and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$), an irreducible $\varpi_0 \in R_0$ mapping to $\varpi.\varpi$ (`hϖ₀`, `hϖ`), the hypothesis `hex` that $\varpi$ is exhausted, i.e. every point of the Drinfeld upper half plane $\Omega = C \setminus \operatorname{im}(K_0 \to C)$ lies in one of the affinoids `Omega.affinoid ϖ n`, and `hϖr` that $v(\varpi.\varpi) = v(r)$ in $C$.
--
--   **Group, tree and quotient data.** $G$ is a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on $\Omega$ (functions which on each affinoid are uniform limits of uniformly bounded pole-free rational functions) is a domain, and $\mathrm{PGL}_2(K_0)$ acts on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` of homothety classes of full lattices by graph automorphisms. A subgroup $\Gamma \le G$ is given with `htp`: the image $H := \rho(\Gamma)$ lies in the type-preserving subgroup, the elements preserving the parity of the tree distance from the standard vertex; $H$ too acts on the tree by graph automorphisms; `hfin`: every dart stabiliser in $H$ is finite; and `htame`: for every vertex $w$ the cardinality of the stabiliser of $w$ in $H$, viewed in $C$, has valuation $1$.
--
--   **The curve.** $FC$ is a field over $C$ with `IsCurveOver C FC` (principal divisors exist, every place has residue field finite over $C$, and $\Omega_{FC/C}$ is free of rank one), `eFC` is a $C$-algebra isomorphism of $FC$ with the field of $\Gamma$-invariants in $\operatorname{Frac}$ of `Omega.HolRingOf ϖ ρ`, and `hfg` asserts that $FC$ contains an element transcendental over $C$ over which $FC$ is finite.
--
--   **The degeneracy datum.** $E$ and $V$ are finite types and $D$ is a `DegeneracyData E V`, i.e. maps $a, b : E \to V$ and widths $w : E \to \mathbb N^{+}$. The bijection `eV` identifies $V$ with the set of $H$-orbits of vertices, and `eE` identifies $E$ with the set of those $H$-orbits of darts whose chosen representative has source of vertex type $0$. The compatibilities `hDa`, `hDb`, `hDw` say that for such an orbit $e$, $D.a$ and $D.b$ at $eE(e)$ are the vertex orbits of the source, resp. the target, of the representative dart, and $D.w$ at $eE(e)$ is the cardinality of the stabiliser in $H$ of that dart. Write $Z :=$ `ribbonKernel D`, the submodule of $(E \to \mathbb Z)$ cut out by the two pushforward maps along $a$ and $b$.
--
--   **The cycle map.** A base vertex $v_0$ and an additive map $\Phi$ from $\mathrm{Additive}(H^{\mathrm{ab}})$ to $Z$ are given, subject to `hΦ`: for $\gamma \in H$ and an edge $e$ as above, the $eE(e)$-coordinate of $\Phi$ of the class of $\gamma$ equals `Mumford.pathCycle` evaluated at $e$, the signed number of darts in the orbit of $e$ traversed by a chosen path from $v_0$ to $\gamma \cdot v_0$.
--
--   **Points of the curve.** A map `pt` from $\Omega$ to the places of $FC$ over $C$ is given, whose fibres are exactly the $H$-orbits (`hpt_fib`) and which is surjective (`hpt_onto`). The hypothesis `hpt` has two clauses: an element $x \in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ precisely when its image under `eFC` is represented in $\operatorname{Frac}$ by a quotient $g/h$ of holomorphic functions with $h$ a non-zero-divisor and $h(z) \ne 0$; and for every invariant quotient $g/h$ with $h(z) \ne 0$, the value of the corresponding element of $FC$ at $\mathrm{pt}(z)$ (via `Place.evalAt`) is $g(z)/h(z)$, and that element lies in the nonunits of the valuation subring of $\mathrm{pt}(z)$ if and only if $g(z) = 0$.
--
--   **The semilinear $S$-action.** `galFC : S →* SemilinearAut C FC` is a homomorphism into the group of pairs of ring automorphisms of $FC$ and of $C$ compatible with the structure map, with `hgalFC_base`: the base automorphism of $galFC(\sigma)$ acts on $C$ as $\mathrm{scalar}(\sigma)$. The hypothesis `hgal` says that every $\sigma \in S$ is implemented on the invariant field by a pair $(n, t)$, with $n$ in the normalizer of $\Gamma$ in $G$ and $t$ an isometric automorphism of $C$ fixing $K_0$ pointwise, so that transport of $galFC(\sigma) \cdot y$ through `eFC` equals $n$ acting on the image of $y$ under the induced automorphism of $\operatorname{Frac}$ of `Omega.HolRingOf ϖ ρ`.
--
--   **Combinatorial shadow of the $S$-action.** Homomorphisms $\pi_V : S \to \mathrm{Perm}(V)$, $\pi_E : S \to \mathrm{Perm}(E)$ and $\mathrm{sgn} : S \to \mathbb Z^{\times}$ are given with: `hπV`, whenever $\sigma$ is implemented by $(n,t)$ as in `hgal`, $\pi_V(\sigma)$ sends the orbit of a vertex $v$ to the orbit of $\rho(n) \cdot v$; `hπE`, for such $(n,t)$ and every type-$0$ dart orbit $e$, if $\rho(n)$ is type-preserving then $\mathrm{sgn}(\sigma) = 1$ and $\pi_E(\sigma)$ sends $e$ to the orbit of $\rho(n) \cdot e$, while if $\rho(n)$ is not type-preserving then $\mathrm{sgn}(\sigma) = -1$ and $\pi_E(\sigma)$ sends $e$ to the orbit of the reversal of $\rho(n) \cdot e$; `hπ_width`, the widths are $\pi_E$-invariant; `hsgn_pos` and `hsgn_neg`, $\pi_E$ commutes with $(a,b)$ when $\mathrm{sgn}(\sigma) = 1$ and swaps them when $\mathrm{sgn}(\sigma) = -1$; and `hπ_inertia`, for $\tau$ in the decomposition group whose underlying automorphism of $\overline{\mathbb Q}$ lies in the inertia subgroup of $A$, one has $\pi_V(\iota\tau) = 1$, $\pi_E(\iota\tau) = 1$ and $\mathrm{sgn}(\iota\tau) = 1$. Finally `actZ : S →* (Z ≃ₗ[ℤ] Z)` is a linear action with `hactZ`: the $\pi_E(\sigma)(e)$-coordinate of $actZ(\sigma)x$ is $\mathrm{sgn}(\sigma)$ times the $e$-coordinate of $x$.
--
--   **Conclusion.** There exists an `EquivariantUniformization r D A hA (Pic0 C FC) S scalar actZ gal`, where the target group is $\mathrm{Pic}^0$ of $FC$ over $C$ (degree-zero divisors modulo principal ones) and $gal$ is the composite of `galFC` with the action of semilinear automorphisms on $\mathrm{Pic}^0$ by additive automorphisms. Such a structure $\mathcal U$ consists of: an intermediate field $\mathcal U.K$ between $\mathbb Q$ and $C$; a homomorphism $\mathrm{ord} : \mathrm{Additive}\,(\mathcal U.K)^{\times} \to \mathbb Z$ with $v(k) = v(r)^{\mathrm{ord}(k)}$; pointwise invariance of $\mathcal U.K$ under every $\mathbb Q$-algebra automorphism of $C$ inducing an inertia element; divisibility of units of $\mathcal U.K$ of $\mathrm{ord}$ zero by every $n > 0$ prime to $r$; a period datum $\mathcal U.P$, i.e. a symmetric $\mathbb Z$-bilinear $Q : Z \times Z \to \mathrm{Additive}\,(\mathcal U.K)^{\times}$ with $\mathrm{ord}\,Q$ the ribbon Gram form of $D$; a surjective additive map $\mathcal U.eFull$ from the torus points $\mathrm{Hom}_{\mathbb Z}(Z, \mathrm{Additive}\,C^{\times})$ onto $\mathrm{Pic}^0$ whose kernel is exactly the period lattice; and equivariance of $Q$ and of $\mathcal U.eFull$ for $S$ acting through `scalar`, `actZ` and $gal$. The structure produced satisfies three further properties.
--
--   First, for every $z \in \mathrm{Pic}^0$ fixed by $galFC(\iota\tau)$ for all $\tau$ in the decomposition group lying in the inertia subgroup, there is a torus point $u$ such that $\mathcal U.P.\mathrm{coeffMap}(s)(u) = u$ for every such $\tau$ and every $\mathbb Q$-algebra automorphism $s$ of $C$ acting as $\tau$, and $\mathcal U.eFull(u) = z$.
--
--   Second, for all $x, y \in \Omega$ such that no $\gamma \in H$ carries $x$ to $y$ under the projective Möbius action, and all $\alpha, \beta \in H$, the image in $C$ of the unit $Q(\Phi[\alpha], \Phi[\beta])$ of $\mathcal U.K$ multiplied by `Omega.period` of the inclusion $H \le \mathrm{PGL}_2(K_0)$ at $(x, y, \alpha, \beta)$ — that is, the theta function with divisor parameters $x$ and $\alpha x$, base point $y$, evaluated at $\beta y$ — equals $1$.
--
--   Third, for all $a, b, z_0 \in \Omega$ with $z_0$ outside the $H$-orbit of $a$ and outside the $H$-orbit of $b$, every homomorphism $c : H \to C^{\times}$ whose value at $\beta$ is `Omega.theta` of $(a, b, z_0)$ evaluated at $\beta z_0$, every torus point $u$ with $u(\Phi[\gamma]) = c(\gamma)$ for all $\gamma \in H$, and every degree-zero divisor $Dv$ equal to $\mathrm{pt}(a) - \mathrm{pt}(b)$, one has $\mathcal U.eFull(u) = [Dv]$ in $\mathrm{Pic}^0$.
--
--   This is the Manin–Drinfeld uniformisation of the Jacobian of the curve obtained as a Mumford quotient of Drinfeld's upper half plane, in equivariant form: the uniformising torus is built from the ribbon (cycle) lattice of the quotient graph of the Bruhat–Tits tree, the period pairing is identified with the inverse of the Manin–Drinfeld periods of the group, and the uniformising map is pinned down on divisor classes $\mathrm{pt}(a) - \mathrm{pt}(b)$ by the multipliers of the corresponding theta function. It is used in the Čerednik–Drinfeld part of the argument, and is cited by the version that produces such a uniformisation naturally in a family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one.lean

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
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega AlgebraicCurve ModularCurve
open CerednikDrinfeld.Mumford

theorem AlgebraicCurve.Pic0.exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one

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
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∃ 𝒰 : EquivariantUniformization r D A hA (Pic0 A.valuation.Completion FC) S scalar actZ
        ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC),

      (∀ z : Pic0 A.valuation.Completion FC,
        (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → galFC (ι τ) • z = z) →
        ∃ u : 𝒰.P.TorusPoints,
          (∀ τ : ↥(A.decompositionSubgroup ℚ),
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
            ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) → 𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
          𝒰.eFull u = z) ∧

      (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (𝒰.P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1) ∧

      (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰.P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          𝒰.eFull u = Pic0.mk Dv) := by sorry
