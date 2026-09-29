-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
-- name    : CerednikDrinfeld.Mumford.addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/85f79669-4190-5da1-b29a-b7c493ed9b4b
-- title:
--   Equality of additive maps from periods and differences of places
-- statement:
--   Fix a prime $r$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $r$ a non-unit of $A$, and write $C = A.\mathrm{valuation.Completion}$ for the completion of the associated valued field. Let $K_0$ be a field with an algebra map to $C$, and let $FC$ be a field over $C$ which is a curve over $C$ in the sense of `IsCurveOver`: principal divisors exist, every place has residue field finite over $C$, and $\Omega_{FC/C}$ is free of rank one over $FC$. Let $E$, $V$ be finite types and $D$ a degeneracy datum on them (source and target maps $E \to V$ and positive weights on $E$), let $\mathrm{pt}$ be a surjection from Drinfeld's upper half-plane $\mathrm{upperHalfPlane}\,K_0\,C$ (the complement in $C$ of the image of $K_0$) onto the places of $FC$, let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ inside $C$, let $\mathrm{ord} : \mathrm{Additive}\,K^\times \to \mathbb{Z}$ be additive, and let $P$ be a period datum for $D$ over $K \subseteq C$ relative to $\mathrm{ord}$, i.e. a symmetric $\mathbb{Z}$-bilinear form $Q$ on $\mathrm{ribbonKernel}\,D$ with values in $\mathrm{Additive}\,K^\times$ whose $\mathrm{ord}$ computes the ribbon Gram form. The torus points are $P.\mathrm{TorusPoints} = \mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}\,D, \mathrm{Additive}\,C^\times)$ and the period lattice is the range of $P.\mathrm{QL}$. Assume $eFull : P.\mathrm{TorusPoints} \to \mathrm{Pic}^0$ (degree-zero divisors of $FC/C$ modulo principal ones) is a surjective additive map whose vanishing locus is exactly the period lattice. Let $T$ be an abelian group and $f, g : P.\mathrm{TorusPoints} \to T$ additive maps such that $f(P.\mathrm{QL}\,z) = g(P.\mathrm{QL}\,z)$ for every $z \in \mathrm{ribbonKernel}\,D$, and such that $f(u) = g(u)$ whenever $eFull(u)$ is the class of a degree-zero divisor equal to $\delta_{\mathrm{pt}\,a} - \delta_{\mathrm{pt}\,b}$ for some $a, b$ in the upper half-plane. Then $f = g$.
--
--   This is the rigidity step in the Mumford-uniformisation part of the Čerednik–Drinfeld package: an additive map out of the torus points $\mathrm{Hom}(\mathrm{ribbonKernel}\,D, C^\times)$ is pinned down by its values on the period lattice together with its values on the points whose image in $\mathrm{Pic}^0$ is the class of a difference of two rational places. It is used to establish equivariance of the uniformisation attached to a period datum for a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ValuationSubring_CompletionDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Mumford.addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion]
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC) (hpt_onto : Function.Surjective pt)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC) (hsurj : Function.Surjective eFull)
    (hker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice)
    (T : Type) [AddCommGroup T] (f g : P.TorusPoints →+ T)
    (hΛ : ∀ z : ↥(ribbonKernel D), f (P.QL z) = g (P.QL z))
    (hdiff : ∀ (u : P.TorusPoints) (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC)),
      (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt a) 1 - Finsupp.single (pt b) 1 → eFull u = Pic0.mk Dv → f u = g u) :
    f = g := by sorry
