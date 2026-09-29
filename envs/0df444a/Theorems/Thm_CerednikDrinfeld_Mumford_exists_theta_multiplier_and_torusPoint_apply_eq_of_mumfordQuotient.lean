-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient
-- name    : CerednikDrinfeld.Mumford.exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/750d0b08-be8e-5bc4-9433-83746edd7da0
-- title:
--   Pinned theta multipliers exist for every pair of points
-- statement:
--   Fix a prime $r$ and a valuation subring $A$ of $\overline{\mathbb Q}$ for which $r$ is a nonunit of $A$, and write $C$ for the completion of $\overline{\mathbb Q}$ at the valuation of $A$. The data are: a group $S$ with homomorphisms $\mathrm{scalar}\colon S\to D$ and $\iota\colon D\to S$, where $D$ is the decomposition subgroup of $A$ over $\mathbb Q$, such that $\mathrm{scalar}\circ\iota=\mathrm{id}$; a field $K_0$ with an algebra map to $C$; a discrete valuation ring $R_0$ with finite residue field and fraction field $K_0$ whose image in $K_0$ is exactly $\{x : v(x)\le 1\}$; a pseudo-uniformizer $\varpi$ of $K_0$ in $C$ (an element with $0<v(\varpi)<1$ whose powers bound the absolute value of every nonzero element of $K_0$ from both sides), an irreducible $\varpi_0\in R_0$ mapping to $\varpi$, the hypothesis that $\varpi$ is exhausted (every point of $\Omega=C\setminus K_0$ lies in some affinoid $\mathrm{affinoid}\ \varpi\ n$), and $v(\varpi)=v(r)$; a group $G$ and $\rho\colon G\to \mathrm{PGL}_2(K_0)$ with holomorphic ring $\mathrm{HolRingOf}\ \varpi\ \rho$ (the ring of functions on $\Omega$ holomorphic on each affinoid) a domain, together with graph actions on the Bruhat–Tits tree of $R_0$; a subgroup $\Gamma\le G$ with $\rho(\Gamma)$ type-preserving (it preserves the parity of the distance to the standard vertex) and with all dart stabilisers in $\rho(\Gamma)$ finite; a field $FC$ which is a curve over $C$ (principal divisors of degree zero, finite residue extensions at all places, $\Omega[FC/C]$ free of rank one), an isomorphism $e_{FC}$ of $FC$ over $C$ with the $\Gamma$-invariant subfield of the fraction field of the holomorphic ring, and a transcendental element over which $FC$ is finite; finite types $E,V$, a degeneracy datum $D=(a,b,w)$ on them, equivalences $e_V$ from vertex orbits to $V$ and $e_E$ from edge orbits of even type to $E$ matching $D.a$, $D.b$ with the orbits of the endpoints of representative darts and $D.w$ with the cardinalities of their stabilisers; a vertex $v_0$ and an additive map $\Phi$ from the abelianisation of $\rho(\Gamma)$ to the ribbon kernel of $D$ (the intersection of the kernels of the pushforwards along $a$ and $b$) computing, on each $\gamma$, the signed dart counts of a chosen path from $v_0$ to $\gamma\cdot v_0$; a map $pt$ from $\Omega$ onto the places of $FC$ over $C$ whose fibres are exactly the $\rho(\Gamma)$-orbits, together with the two clauses identifying the valuation ring at $pt\,z$ with the quotients $g/h$ of holomorphic functions with $h(z)\ne0$ and the evaluation at $pt\,z$ with $g(z)/h(z)$, the nonunits being those with $g(z)=0$; and, for an intermediate field $K$ of $\mathbb Q\subset C$ and a homomorphism $\mathrm{ord}\colon \mathrm{Additive}\,K^\times\to\mathbb Z$, a period datum $P$ for $D$ over $K\subset C$ (a symmetric $\mathbb Z$-bilinear $Q$ on the ribbon kernel with values in $K^\times$ whose $\mathrm{ord}$ is the ribbon Gram form). The conclusion: for all $a,b\in\Omega$ there is a point $z_0\in\Omega$ lying in neither the $\rho(\Gamma)$-orbit of $a$ nor that of $b$, a homomorphism $c\colon\rho(\Gamma)\to C^\times$ with $c(\beta)=\Theta(a,b;z_0)(\beta z_0)$ for all $\beta$, where $\Theta$ is the infinite product of cross-ratio factors over $\rho(\Gamma)$, and a torus point $u\in\mathrm{Hom}_{\mathbb Z}(\mathrm{ribbonKernel}\ D,\ \mathrm{Additive}\,C^\times)$ with $u(\Phi(\bar\gamma))=c(\gamma)$ for every $\gamma\in\rho(\Gamma)$.
--
--   This is the existence statement for theta data on a Mumford quotient pinned to the torus of the analytic uniformisation: every pair of points of Drinfeld's upper half plane admits an admissible base point $z_0$ whose theta multiplier factors through the cycle map $\Phi$ into the character group of the ribbon kernel. It feeds [`AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient), where the pinning clause is what identifies divisor classes $[pt\,a-pt\,b]$ with points of the Mumford torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient.lean

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

theorem CerednikDrinfeld.Mumford.exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient

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
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord) :
    ∀ (a b : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
      ∃ (z₀ : A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) ∧ (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) ∧
        ∃ c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ,
          (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) ∧
          ∃ u : P.TorusPoints, ∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ) := by sorry
