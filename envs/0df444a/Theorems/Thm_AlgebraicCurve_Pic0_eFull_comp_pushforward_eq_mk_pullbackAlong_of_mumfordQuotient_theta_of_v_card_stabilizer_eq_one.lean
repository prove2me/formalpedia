-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/559c6bef-e4be-5172-b950-ad8bffcabcec
-- title:
--   Pullback compatibility of pinned Mumford uniformisations of Pic⁰
-- statement:
--   Write $C = A.\mathrm{valuation}.\mathrm{Completion}$ for the completion attached to a valuation subring $A$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, and $\Omega =$ `Omega.upperHalfPlane K₀ C`, the complement in $C$ of the image of $K_0$.
--
--   *Residual and arithmetic data.* A prime $r$; a valuation subring $A$ of $\overline{\mathbb Q}$ together with `hA : A.LiesOverPrime r`, i.e. $r$ lies in the non-units of $A$; a field $K_0$ with a $C$-algebra structure map; a discrete valuation ring $R_0$ which is a domain with finite residue field and fraction field $K_0$; the hypothesis `hR₀`, that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation $\le 1$; a pseudo-uniformiser $\varpi$ of $K_0$ relative to $C$ (an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$, with the scaling clause of `Omega.PseudoUniformizer`); an irreducible $\varpi_0 \in R_0$ with image $\varpi.\varpi$ (`hϖ₀`, `hϖ`); `hex`, that $\varpi$ is exhausting, i.e. every point of $\Omega$ lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr`, that the valuation of $\varpi.\varpi$ in $C$ equals that of $r$.
--
--   *Group and tree data.* A group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring `Omega.HolRingOf ϖ ρ` of functions on $\Omega$ holomorphic on every affinoid is a domain, an action of $\mathrm{PGL}_2(K_0)$ on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` respecting adjacency, and a vertex $v_0$ of that tree.
--
--   *Level data, at each of the two levels $x \in \{d,c\}$ (variables $\Gamma_d,\dots$ and $\Gamma_c,\dots$, the clauses being identical in shape).* A subgroup $\Gamma_x \le G$ whose image $H_x := \rho(\Gamma_x)$ is type-preserving (`htpd`, `htpc`: every element of $H_x$ preserves the parity of the distance from the standard vertex), acts on the tree respecting adjacency, and has finite dart stabilisers (`hfind`, `hfinc`); the tameness hypotheses `htamed`, `htamec`, that for every vertex $w$ the cardinality of the $H_x$-stabiliser of $w$ has valuation $1$ in $C$. A field $F_x$ over $C$ which is a curve over $C$ in the sense of `IsCurveOver` (principal divisors exist, all residue fields of places are finite over $C$, and $\Omega^1_{F_x/C}$ is free of rank one), together with a $C$-algebra isomorphism $e_{F_x}$ of $F_x$ onto the invariant subfield `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γx` of $\mathrm{Frac}(\mathcal O(\Omega))$. Finite types $E_x, V_x$ and a degeneracy datum $D_x$ on them (maps $a,b : E_x \to V_x$ and weights $w : E_x \to \mathbb N_{>0}$), presented as the folded quotient graph: a bijection $e_{V_x}$ from the set of $H_x$-orbits of vertices onto $V_x$, a bijection $e_{E_x}$ from the set of $H_x$-orbits of darts whose chosen representative has first vertex of type $0$ onto $E_x$, and the compatibilities `hDad`/`hDac`, `hDbd`/`hDbc`, `hDwd`/`hDwc`, stating that under these bijections $a$ and $b$ compute the orbits of the first and second vertex of a dart and $w$ computes the cardinality of the dart stabiliser. A homomorphism $\Phi_x$ from the additive group of the abelianisation of $H_x$ to the cycle lattice `ribbonKernel Dx` (the intersection of the kernels of the two joint delta maps inside $E_x \to \mathbb Z$), pinned by `hΦd`/`hΦc` to the winding numbers: the $e$-coordinate of $\Phi_x(\gamma)$ is the value at $e$ of `Mumford.pathCycle` for a path from $v_0$ to $\gamma \cdot v_0$. A map $\mathrm{pt}_x$ from $\Omega$ to the places of $F_x$ over $C$ whose fibres are exactly the $H_x$-orbits (`hpt_fibd`, `hpt_fibc`) and which is surjective (`hpt_ontod`, `hpt_ontoc`); and the analytic description `hptd`, `hptc` of these places, in two clauses: for $z \in \Omega$, an element $x \in F_x$ lies in the valuation subring of $\mathrm{pt}_x(z)$ precisely when $e_{F_x}(x)$ can be written as $g/h$ with $g,h$ holomorphic, $h$ a non-zero-divisor and $h(z) \ne 0$; and for such a fraction lying in the invariant field, its value at $\mathrm{pt}_x(z)$ is $g(z)/h(z)$, and it lies in the maximal ideal of that valuation subring exactly when $g(z) = 0$.
--
--   *Equivariance data.* A group $S$ with a homomorphism $\mathrm{scalar}$ into the decomposition subgroup of $A$ over $\mathbb Q$; homomorphisms $\mathrm{actZ}_d, \mathrm{actZ}_c$ of $S$ into the groups of $\mathbb Z$-linear automorphisms of the cycle lattices of $D_d$, $D_c$; homomorphisms $\mathrm{gal}_d, \mathrm{gal}_c$ of $S$ into the semilinear automorphism groups `SemilinearAut C Fd`, `SemilinearAut C Fc` (pairs of ring automorphisms of $F_x$ and of $C$ compatible with the structure map); and equivariant uniformisations $\mathcal U_d$, $\mathcal U_c$ of $\mathrm{Pic}^0(F_d)$, $\mathrm{Pic}^0(F_c)$ for $r$, $D_d$, $D_c$, $A$, $hA$, $S$, $\mathrm{scalar}$, $\mathrm{actZ}_x$ and the induced additive actions of $\mathrm{gal}_x$ on $\mathrm{Pic}^0$. Each $\mathcal U_x$ consists of an intermediate field $\mathcal U_x.K$ of $C$ over $\mathbb Q$ with an order homomorphism normalising valuations by powers of $v(r)$, inertia-invariance and Hensel clauses, a period datum $\mathcal U_x.P$ for $D_x$ with period pairing $Q$, and a surjective homomorphism $\mathcal U_x.\mathrm{eFull}$ from the torus points (the $\mathbb Z$-linear maps from the cycle lattice to $\mathrm{Additive}\,C^\times$) onto $\mathrm{Pic}^0(F_x)$ whose kernel is the period lattice, together with the $S$-equivariance of $Q$ and of $\mathrm{eFull}$.
--
--   *Pinning of the uniformisations to the analytic periods and thetas.* The hypotheses `hQd`, `hQc`: for $x, y \in \Omega$ with $y$ not in the $H_x$-orbit of $x$ and all $\alpha,\beta \in H_x$, the image in $C$ of $Q(\Phi_x(\alpha), \Phi_x(\beta))$ times the analytic period `Omega.period` of $(x,y,\alpha,\beta)$ for $H_x$ equals $1$. The hypotheses `hΘd`, `hΘc`: for $a,b,z_0 \in \Omega$ with neither $a$ nor $b$ in the $H_x$-orbit of $z_0$, for every character $c : H_x \to C^\times$ whose value at $\beta$ is the theta function `Omega.theta` of $(a,b,z_0)$ evaluated at $\beta \cdot z_0$, for every torus point $u$ with $u(\Phi_x(\gamma)) = c(\gamma)$ for all $\gamma$, and for every degree-zero divisor $D_v$ whose underlying divisor is $\mathrm{pt}_x(a) - \mathrm{pt}_x(b)$, one has $\mathcal U_x.\mathrm{eFull}(u) = [D_v]$ in $\mathrm{Pic}^0$.
--
--   *The arrow.* An element $g \in G$ whose image $\rho(g)$ is type-preserving (`hg`), with $\Gamma_d \le g\Gamma_c g^{-1}$ (`hArr`); a $C$-algebra homomorphism $\varphi : F_c \to F_d$ which, under the identifications $e_{F_c}$, $e_{F_d}$, is given by the action of $g$ on $\mathrm{Frac}(\mathcal O(\Omega))$ (`hφ`); the hypotheses `hφC` that $\varphi$ is integral, `hfinC` that $F_d$ is a finite $F_c$-module along $\varphi$, and `hsepC` that it is separable along $\varphi$. A finite homomorphism $\mu : D_d \to D_c$ of degeneracy data (maps $\mathrm{mapV}$, $\mathrm{mapE}$ commuting with $a$ and $b$, local degrees $\deg$ on edges, vertex degrees $\deg V$ and a total degree, subject to $w(\mu e) = \deg(e)\,w(e)$ and the fibrewise degree-sum identities of `DegeneracyData.FiniteHom`), matched with $g$ by `hμV` and `hμE`: on vertex orbits $\mu.\mathrm{mapV}$ sends the $H_d$-orbit of $v$ to the $H_c$-orbit of $\rho(g)^{-1} \cdot v$, and on edges $\mu.\mathrm{mapE}$ sends the class of $e$ to the $H_c$-orbit of the dart $\rho(g)^{-1} \cdot e$; and `hdeg`, that the total degree of $\mu$ equals the degree $[F_d : F_c]$ along $\varphi$. Finally the projection hypothesis `hproj`: for all $x$ in the cycle lattice of $D_c$ and $y$ in that of $D_d$, the images in $C$ of $Q_d(\mu.\mathrm{pullback}\,x, y)$ and of $Q_c(x, \mu.\mathrm{pushforward}\,y)$ coincide.
--
--   *Conclusion.* For every torus point $u$ of $\mathcal U_c.P$, every degree-zero divisor $D_1$ on $F_c$ and every degree-zero divisor $D_1'$ on $F_d$: if $\mathcal U_c.\mathrm{eFull}(u) = [D_1]$ in $\mathrm{Pic}^0(F_c)$ and the divisor underlying $D_1'$ is the pullback `Divisor.pullbackAlong φ hφC` of the divisor underlying $D_1$ (each place of $F_c$ replaced by the sum of the places of $F_d$ above it, weighted by their ramification indices), then $\mathcal U_d.\mathrm{eFull}$ of the torus point $u \circ \mu.\mathrm{pushforward}$ equals $[D_1']$ in $\mathrm{Pic}^0(F_d)$.
--
--   This is the pullback (conorm) half of the naturality of the Čerednik–Drinfel'd/Mumford uniformisation along a degeneracy map of levels: composing a torus point with the push-forward on cycle lattices computes the pullback of divisor classes along the corresponding morphism of Mumford quotients. It is used, together with its push-forward counterpart, by [`AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one) to produce a family of equivariant uniformisations compatible with the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
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
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Pic0.eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)

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
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)

    (Γd : Subgroup G) (htpd : Γd.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfind : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γd.map ρ)) d))

    (htamed : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γd.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (Fd : Type) [Field Fd] [Algebra A.valuation.Completion Fd] [hcurved : IsCurveOver A.valuation.Completion Fd]
    (eFd : Fd ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd))

    (Ed Vd : Type) [Fintype Ed] [Fintype Vd] [DecidableEq Ed] [DecidableEq Vd]
    (Dd : DegeneracyData Ed Vd)
    (eVd : Mumford.QuotVert ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vd)
    (eEd : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ed)
    (hDad : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.a (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.b (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dd.w (eEd e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γd.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φd : Additive (Abelianization ↥(Γd.map ρ)) →+ ↥(ribbonKernel Dd))
    (hΦd : ∀ γ : ↥(Γd.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φd (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dd)) : Ed → ℤ) (eEd e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptd : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fd)
    (hpt_fibd : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptd z = ptd z' ↔ ∃ γ : ↥(Γd.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontod : Function.Surjective ptd)

    (hptd : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fd),
        x ∈ (ptd z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFd x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptd z).evalAt (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptd z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (Γc : Subgroup G) (htpc : Γc.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfinc : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γc.map ρ)) d))

    (htamec : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γc.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (Fc : Type) [Field Fc] [Algebra A.valuation.Completion Fc] [hcurvec : IsCurveOver A.valuation.Completion Fc]
    (eFc : Fc ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc))

    (Ec Vc : Type) [Fintype Ec] [Fintype Vc] [DecidableEq Ec] [DecidableEq Vc]
    (Dc : DegeneracyData Ec Vc)
    (eVc : Mumford.QuotVert ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vc)
    (eEc : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ec)
    (hDac : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.a (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.b (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dc.w (eEc e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γc.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φc : Additive (Abelianization ↥(Γc.map ρ)) →+ ↥(ribbonKernel Dc))
    (hΦc : ∀ γ : ↥(Γc.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φc (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dc)) : Ec → ℤ) (eEc e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptc : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fc)
    (hpt_fibc : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptc z = ptc z' ↔ ∃ γ : ↥(Γc.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontoc : Function.Surjective ptc)

    (hptc : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fc),
        x ∈ (ptc z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptc z).evalAt (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptc z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZd : S →* (↥(ribbonKernel Dd) ≃ₗ[ℤ] ↥(ribbonKernel Dd))) (gald : S →* SemilinearAut A.valuation.Completion Fd)
    (actZc : S →* (↥(ribbonKernel Dc) ≃ₗ[ℤ] ↥(ribbonKernel Dc))) (galc : S →* SemilinearAut A.valuation.Completion Fc)
    (𝒰d : EquivariantUniformization r Dd A hA (Pic0 A.valuation.Completion Fd) S scalar actZd
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fd) (Pic0 A.valuation.Completion Fd)).comp gald))
    (𝒰c : EquivariantUniformization r Dc A hA (Pic0 A.valuation.Completion Fc) S scalar actZc
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fc) (Pic0 A.valuation.Completion Fc)).comp galc))
    (hQd : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γd.map ρ),
          ((((Additive.toMul (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of α))) (Φd (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) * Omega.period (Γd.map ρ).subtype x y α β = 1))
    (hΘd : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γd.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γd.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γd.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰d.P.TorusPoints), (∀ γ : ↥(Γd.map ρ), u (Φd (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd),
          (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd ⟨a, ha⟩) 1 - Finsupp.single (ptd ⟨b, hb⟩) 1 →
          𝒰d.eFull u = Pic0.mk Dv))
    (hQc : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γc.map ρ),
          ((((Additive.toMul (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of α))) (Φc (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) * Omega.period (Γc.map ρ).subtype x y α β = 1))
    (hΘc : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γc.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γc.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γc.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰c.P.TorusPoints), (∀ γ : ↥(Γc.map ρ), u (Φc (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fc),
          (Dv : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc ⟨a, ha⟩) 1 - Finsupp.single (ptc ⟨b, hb⟩) 1 →
          𝒰c.eFull u = Pic0.mk Dv))

    (g : G) (hg : ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) (hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom)
    (φ : Fc →ₐ[A.valuation.Completion] Fd)
    (hφ : ∀ x : Fc, ((eFd (φ x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral) (hfinC : FiniteAlong A.valuation.Completion φ) (hsepC : SeparableAlong A.valuation.Completion φ)
    (μ : Dd.FiniteHom Dc)
    (hμV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, μ.mapV (eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) =
      eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ g)⁻¹ • v)))
    (hμE : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, ((eEc.symm (μ.mapE (eEd e))).1) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ g)⁻¹ • e.1.out))
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ)

    (hproj : ∀ (x : ↥(ribbonKernel Dc)) (y : ↥(ribbonKernel Dd)),
      ((((Additive.toMul (𝒰d.P.Q (μ.pullback x) y)) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) =
        ((((Additive.toMul (𝒰c.P.Q x (μ.pushforward y))) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion)) :
    ∀ (u : 𝒰c.P.TorusPoints) (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := Fc)) (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := Fd)),
      𝒰c.eFull u = Pic0.mk D₁ →
      (D₁' : Divisor A.valuation.Completion Fd) = Divisor.pullbackAlong φ hφC (D₁ : Divisor A.valuation.Completion Fc) →
      𝒰d.eFull (u.comp μ.pushforward) = Pic0.mk D₁' := by sorry
