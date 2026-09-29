-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq
-- name    : CerednikDrinfeld.Mumford.exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/97921491-8782-5948-85bc-6a7df56f667c
-- title:
--   Galois transport of a theta-pinned Mumford torus point
-- statement:
--   Throughout, $C$ denotes the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ with respect to the valuation of a valuation subring $A$, and $\Omega =$ `Omega.upperHalfPlane K₀ C` denotes the complement in $C$ of the image of $K_0$, Drinfeld's upper half plane, on which $PGL(2,K_0)$ acts through `Omega.pmoebius` (the Möbius action on $\mathbb P^1(C)$ read in the affine coordinate).
--
--   Arithmetic frame. A prime $r$; a valuation subring $A$ of $\overline{\mathbb Q}$ with `hA` asserting that $r$ is a nonunit of $A$; a group $S$ with a homomorphism `scalar` from $S$ to the decomposition subgroup of $A$ over $\mathbb Q$ and a homomorphism $\iota$ in the other direction which splits it, `hι` : $\mathrm{scalar}(\iota\tau)=\tau$ for all $\tau$.
--
--   Local data. A field $K_0$ with a structure map into $C$; a discrete valuation domain $R_0$ with fraction field $K_0$ and finite residue field, such that `hR₀`: an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation $\le 1$. A pseudo-uniformiser $\varpi$ of $K_0$ relative to $C$, that is an element $\varpi.\varpi\in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that for every nonzero $a\in K_0$ some power $N$ satisfies $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$; an irreducible $\varpi_0\in R_0$ (`hϖ₀`) with `hϖ` : $\varpi_0\mapsto\varpi.\varpi$; `hex`, the exhaustion hypothesis that every point of $\Omega$ lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr`, the equality of valuations $v(\varpi.\varpi)=v(r)$ in $C$.
--
--   Group and tree data. A group $G$ with $\rho : G \to PGL(2,K_0)$; the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on $\Omega$ (functions $\Omega\to C$ whose restriction to each affinoid is a bounded uniform limit of pole-free rational functions) is assumed to be a domain; the actions of $PGL(2,K_0)$ and of $\rho(\Gamma)$ on the Bruhat–Tits tree of $R_0\subset K_0$ are graph actions. A subgroup $\Gamma\le G$ with `htp`: the image $\rho(\Gamma)$ lies in `typePreserving`, the subgroup of elements preserving the parity of the distance to the standard vertex; `hfin`: every dart stabiliser in $\rho(\Gamma)$ is finite.
--
--   Curve data. A field $FC$ over $C$ with `hcurve` : `IsCurveOver C FC` — every nonzero element of $FC$ has a divisor of degree zero recording its orders at all places, every place has residue field finite over $C$, and $\Omega^1_{FC/C}$ is free of rank one — together with a $C$-algebra isomorphism $e_{FC}$ from $FC$ onto `invariantFieldOf C G (HolRingOf ϖ ρ) Γ`, the subfield of $\Gamma$-invariants of the fraction field of the holomorphic ring; and `hfg`: there is a transcendental $x\in FC$ over $C$ with $FC$ finite over $C(x)$.
--
--   Combinatorial data. Finite types $E$, $V$ with decidable equality; a degeneracy datum $D$ on $(E,V)$, consisting of maps $D.a, D.b : E\to V$ and widths $D.w : E\to\mathbb N^{+}$; a bijection $e_V$ from the set of $\rho(\Gamma)$-orbits of vertices onto $V$; a bijection $e_E$ from the set of those $\rho(\Gamma)$-orbits of darts whose chosen representative has tail of type $0$ onto $E$; `hDa`, `hDb`, `hDw` identifying, for each such orbit $e$, $D.a(e_E e)$ and $D.b(e_E e)$ with the vertex orbits of the tail and of the head of the representative dart, and $D.w(e_E e)$ with the order of the stabiliser of that dart in $\rho(\Gamma)$. A base vertex $v_0$; a homomorphism $\Phi$ from the additive form of the abelianisation of $\rho(\Gamma)$ to `ribbonKernel D`, the submodule of $E\to\mathbb Z$ cut out by the kernels of the two pushforwards along $D.a$ and $D.b$; and `hΦ`: for every $\gamma\in\rho(\Gamma)$ and every even dart orbit $e$, the coordinate of $\Phi(\bar\gamma)$ at $e_E e$ equals the path cycle `Mumford.pathCycle` of $\gamma$ based at $v_0$, evaluated at $e$, i.e. the signed multiplicity with which a chosen path from $v_0$ to $\gamma\cdot v_0$ traverses the orbit $e$.
--
--   Points of the curve. A map $\mathrm{pt}$ from $\Omega$ to the places of $FC$ over $C$ (a place being a valuation subring of $FC$ containing the image of $C$, not all of $FC$, and a principal ideal ring), with `hpt_fib`: $\mathrm{pt}(z)=\mathrm{pt}(z')$ if and only if $z'=\gamma\cdot z$ for some $\gamma\in\rho(\Gamma)$; `hpt_onto`: $\mathrm{pt}$ is surjective; and `hpt`, a two-clause description of these places: first, $x\in FC$ lies in the valuation subring of $\mathrm{pt}(z)$ exactly when $e_{FC}(x)$ is, in the fraction field of the holomorphic ring, of the form $g/h$ with $g,h$ holomorphic, $h$ a nonzerodivisor and $h(z)\ne 0$; second, for any such fraction $g/h$ lying in the invariant field and with $h(z)\ne 0$, the evaluation of $\mathrm{pt}(z)$ at the corresponding element of $FC$ is $g(z)/h(z)$, and that element lies in the nonunits of $\mathrm{pt}(z)$ precisely when $g(z)=0$.
--
--   Symmetries. A homomorphism $\mathrm{gal}_{FC}$ from $S$ to `SemilinearAut C FC`, the group of pairs consisting of a ring automorphism of $FC$ and one of $C$ compatible with the structure map, with `hgalFC_base`: the base component of $\mathrm{gal}_{FC}(\sigma)$ acts on $C$ as $\mathrm{scalar}(\sigma)$; and `hgal`: every $\sigma\in S$ is realised geometrically, that is there are $n\in G$ in the normaliser of $\Gamma$ and an isometric automorphism $t$ of $C$ (a valuation-preserving ring automorphism fixing $K_0$ pointwise) such that, for all $y\in FC$, $e_{FC}(\mathrm{gal}_{FC}(\sigma)\cdot y) = n\cdot \mathrm{fracMap}(\mathrm{toAmbientOf}\,\varpi\,\rho\,t)(e_{FC}(y))$ in the fraction field of the holomorphic ring. Homomorphisms $\pi_V : S\to\mathrm{Perm}(V)$, $\pi_E : S\to\mathrm{Perm}(E)$ and $\mathrm{sgn} : S\to\mathbb Z^{\times}$, subject to: `hπV`, for every $\sigma$ and every pair $(n,t)$ realising $\sigma$ as above, $\pi_V(\sigma)$ acts on vertex orbits as $\rho(n)$ does; `hπE`, for the same data and every even dart orbit $e$, if $\rho(n)$ is type-preserving then $\mathrm{sgn}(\sigma)=1$ and the orbit indexed by $\pi_E(\sigma)(e_E e)$ is the orbit of $\rho(n)$ applied to the representative dart of $e$, while if $\rho(n)$ is not type-preserving then $\mathrm{sgn}(\sigma)=-1$ and that orbit is the orbit of the reverse of $\rho(n)$ applied to the representative dart; `hπ_width`, $\pi_E$ preserves the widths $D.w$; `hsgn_pos` and `hsgn_neg`, $\pi_E$ intertwines $D.a$ with $D.a$ and $D.b$ with $D.b$ via $\pi_V$ when $\mathrm{sgn}(\sigma)=1$, and interchanges them when $\mathrm{sgn}(\sigma)=-1$; `hπ_inertia`, for $\tau$ in the decomposition subgroup whose underlying automorphism of $\overline{\mathbb Q}$ lies in the inertia subgroup, $\pi_V(\iota\tau)=1$, $\pi_E(\iota\tau)=1$ and $\mathrm{sgn}(\iota\tau)=1$. A homomorphism $\mathrm{act}_{\mathbb Z}$ from $S$ to the $\mathbb Z$-linear automorphisms of `ribbonKernel D` with `hactZ`: $(\mathrm{act}_{\mathbb Z}(\sigma)x)(\pi_E(\sigma)e) = \mathrm{sgn}(\sigma)\, x(e)$ for all $x$ and $e$.
--
--   Period datum. An intermediate field $K$ of $C/\mathbb Q$, a homomorphism $\mathrm{ord}$ from the additive form of $K^{\times}$ to $\mathbb Z$, and a period datum $P$ for $D$ over $K\subset C$ relative to $\mathrm{ord}$: a symmetric $\mathbb Z$-bilinear form $Q$ on `ribbonKernel D` with values in the additive form of $K^{\times}$ whose composite with $\mathrm{ord}$ is the ribbon Gram form of $D$.
--
--   The chosen symmetry and theta datum. An element $\sigma\in S$ and a $\mathbb Q$-algebra automorphism $s$ of $C$ with `hs` : $s(c)=\mathrm{scalar}(\sigma)\cdot c$ for all $c$; an element $n\in G$ in the normaliser of $\Gamma$ (`hn`) and an isometric automorphism $t$ of $C$ over $K_0$ for which `hreal` is the realisation identity of `hgal` for this $\sigma$, $n$ and $t$. Elements $a,b,z_0\in C$ lying in $\Omega$ (`ha`, `hb`, `hz₀`), with `hz₀a` and `hz₀b` asserting that $\gamma\cdot a\ne z_0$ and $\gamma\cdot b\ne z_0$ for every $\gamma\in\rho(\Gamma)$. A homomorphism $c : \rho(\Gamma)\to C^{\times}$ with `hc`: for every $\beta$, $c(\beta)$ equals the theta value $\Theta(a,b;z_0)(\beta\cdot z_0) = \prod'_{\gamma\in\rho(\Gamma)}\mathrm{crossRatio}(\beta\cdot z_0, z_0, \gamma\cdot a, \gamma\cdot b)$ (the product being taken over $\rho(\Gamma)$ through its inclusion into $PGL(2,K_0)$). Finally a torus point $u$ of $P$, that is a $\mathbb Z$-linear map from `ribbonKernel D` to the additive form of $C^{\times}$, pinned to $c$ by `hu`: $u(\Phi(\bar\gamma)) = c(\gamma)$ for every $\gamma\in\rho(\Gamma)$.
--
--   Conclusion. Write $a' = \rho(n)\cdot t(a)$, $b' = \rho(n)\cdot t(b)$ and $z_0' = \rho(n)\cdot t(z_0)$, where $t$ acts through its ring automorphism of $C$ and $\rho(n)$ through the Möbius action. Then the conjunction of the following holds: $a'\in\Omega$; $b'\in\Omega$; $z_0'\in\Omega$; for every $\gamma\in\rho(\Gamma)$ one has $\gamma\cdot a'\ne z_0'$; for every $\gamma\in\rho(\Gamma)$ one has $\gamma\cdot b'\ne z_0'$; and there exists a homomorphism $c' : \rho(\Gamma)\to C^{\times}$ such that, first, $c'(\beta) = \Theta(a',b';z_0')(\beta\cdot z_0')$ for every $\beta\in\rho(\Gamma)$, and second, for every $\gamma\in\rho(\Gamma)$,
--   $$\bigl(P.\mathtt{coeffMap}\,s\,\bigl(P.\mathtt{precomp}\,(\mathrm{act}_{\mathbb Z}(\sigma))^{-1}\,u\bigr)\bigr)(\Phi(\bar\gamma)) = c'(\gamma),$$
--   where `coeffMap` applies $s$ to the values through `Units.map` and `precomp` composes with the inverse of $\mathrm{act}_{\mathbb Z}(\sigma)$; explicitly, the transported torus point $x\mapsto s\bigl(u((\mathrm{act}_{\mathbb Z}(\sigma))^{-1}x)\bigr)$ sends $\Phi(\bar\gamma)$ to $c'(\gamma)$. Thus the transported triple $(a',b';z_0')$ is again an admissible theta datum for $\rho(\Gamma)$, and the transported torus point is pinned to its theta multiplier.
--
--   This is the theta-pinned half of the Galois equivariance of the Manin–Drinfeld period uniformisation of a Mumford quotient of Drinfeld's upper half plane: it transports an admissible theta datum and the torus point pinned to its multiplier along a semilinear symmetry realised by a normalising element $n$ of $\Gamma$ together with an isometric automorphism $t$ of the coefficient field. It is used in [`AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient) to supply the equivariance clause of the uniformisation of the Jacobian of the Mumford curve; the naturality of the cycle map under the normaliser enters through [`CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle`](thm.html#CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle), and the behaviour of the theta product under $t$ and under Möbius transformations through [`CerednikDrinfeld.Omega.theta_isometricAut`](thm.html#CerednikDrinfeld.Omega.theta_isometricAut) and [`CerednikDrinfeld.Omega.crossRatio_pmoebius`](thm.html#CerednikDrinfeld.Omega.crossRatio_pmoebius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq.lean

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
open CerednikDrinfeld
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford
open AlgebraicCurve ModularCurve

theorem CerednikDrinfeld.Mumford.exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq

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
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)

    (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion) (hs : ∀ c, s c = (scalar σ) • c)
    (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion) (hn : n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G))
    (hreal : ∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)))

    (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz₀a : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) (hz₀b : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀)
    (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ) (hc : ∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀))
    (u : P.TorusPoints) (hu : ∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) :
    Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧
    (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a)) ≠ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) ∧
    (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b)) ≠ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) ∧
    ∃ c' : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ,
      (∀ β : ↥(Γ.map ρ), ((c' β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)))) ∧
      (∀ γ : ↥(Γ.map ρ),
        (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
          (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u))
          (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c' γ)) := by sorry
