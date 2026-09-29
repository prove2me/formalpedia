-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
-- name    : AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cad122a0-4842-5005-afe7-a9b45b6f7232
-- title:
--   Push-forward square for pinned Mumford uniformisations along φ
-- statement:
--   Throughout, $r$ is a prime, $A$ is a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime r`, that is $r$ lies in the nonunits of $A$, and $C := A.valuation.Completion$ denotes the completion of $\overline{\mathbb Q}$ at the associated valuation.
--
--   **Local constants.** A field $K_0$ equipped with a map to $C$, and a discrete valuation ring $R_0$ which is a domain with fraction field $K_0$ and finite residue field; `hR₀` says that an element of $K_0$ comes from $R_0$ exactly when its image in $C$ has valuation $\le 1$. Further, a pseudo-uniformizer $\varpi$ for $K_0$ over $C$ (an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$, and such that for each nonzero $a\in K_0$ some power $N$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$), an irreducible $\varpi_0 \in R_0$ with `hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ`, the hypothesis `hex` that $\varpi$ is exhausted (every point of the Drinfeld upper half plane $\Omega := C \setminus \mathrm{im}(K_0)$ lies in some affinoid `Omega.affinoid ϖ n`), and `hϖr` that $v(\varpi.\varpi) = v(r)$ in $C$.
--
--   **Group and tree.** A group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring `Omega.HolRingOf ϖ ρ`, by definition the ring `Omega.holRing ϖ` of functions $\Omega \to C$ holomorphic on each affinoid, is a domain; the action of $\mathrm{PGL}_2(K_0)$ on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` on homothety classes of full lattices is a graph action; and a base vertex $v_0$.
--
--   **Two levels.** The hypotheses come in two parallel blocks, indexed by $d$ and $c$; they are stated here once, with $\Gamma \in \{\Gamma_d,\Gamma_c\}$, $H := \Gamma.map\ \rho$, and correspondingly $F$, $E$, $V$, $D$, $\Phi$, $\mathrm{pt}$ (Lean: `Fd, Ed, Vd, Dd, Φd, ptd` and `Fc, Ec, Vc, Dc, Φc, ptc`). A subgroup $\Gamma \le G$ with `htp` asserting that $H$ consists of type-preserving elements (those fixing the parity of the distance to the standard vertex) and `hfin` asserting that every dart of the tree has finite stabiliser in $H$; a field $F$ over $C$ with `IsCurveOver C F` (principal divisors exist, all residue fields of places are finite over $C$, and $\Omega[F/C]$ is free of rank $1$), together with a $C$-algebra isomorphism $e_F$ of $F$ onto `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ`, the $\Gamma$-invariant subfield of $\operatorname{Frac}$ of the holomorphic ring; finite types $E, V$ and a degeneracy datum $D = (a, b : E \to V,\ w : E \to \mathbb N_{>0})$; bijections $e_V$ from the set of $H$-orbits of vertices to $V$ and $e_E$ from the set of $H$-orbits of darts whose chosen representative has first vertex of type $0$ to $E$; the hypotheses `hDa`, `hDb`, `hDw` identifying, for each such orbit $e$, $a(e_E e)$ with the orbit of the source of the representative dart, $b(e_E e)$ with the orbit of its target, and $w(e_E e)$ with the order of the stabiliser of the representative dart in $H$; a homomorphism $\Phi$ from the additive version of $H^{\mathrm{ab}}$ to `ribbonKernel D`, with `hΦ` asserting that the $e_E e$-coordinate of $\Phi$ of the class of $\gamma$ equals `Mumford.pathCycle` of the tree for the orbit map, base point $v_0$ and element $\gamma$, evaluated at $e$; a map $\mathrm{pt} : \Omega \to$ `Place C F` with `hpt_fib` (two points have the same image exactly when they differ by an element of $H$) and `hpt_onto` (surjectivity); and the two-clause hypothesis `hpt`, which says first that $x \in F$ lies in the valuation subring of $\mathrm{pt}(z)$ precisely when $e_F(x)$ can be written as $g/h$ with $g, h$ in the holomorphic ring, $h$ a non-zero-divisor and $h(z) \ne 0$, and second that for any such $g/h$ lying in the invariant field and with $h(z) \ne 0$ the place evaluation of the corresponding element of $F$ at $\mathrm{pt}(z)$ equals $g(z)/h(z)$, this element lying in the nonunits of the valuation subring of $\mathrm{pt}(z)$ exactly when $g(z) = 0$.
--
--   **Galois data and uniformisations.** A group $S$ with a homomorphism $\mathrm{scalar}$ to the decomposition subgroup of $A$ over $\mathbb Q$, homomorphisms $\mathrm{actZ}_d, \mathrm{actZ}_c$ of $S$ into the $\mathbb Z$-linear automorphism groups of `ribbonKernel Dd`, `ribbonKernel Dc`, and homomorphisms $\mathrm{gal}_d, \mathrm{gal}_c$ of $S$ into the groups of semilinear automorphisms (pairs of ring automorphisms of $F$ and of $C$ compatible with $C \to F$). Finally, equivariant uniformisations $\mathcal U_d$, $\mathcal U_c$ of `Pic0 C Fd`, `Pic0 C Fc` (degree-zero divisor classes modulo principal divisors) over $D_d$, $D_c$, for the prime $r$, the place $A$, the group $S$ and these actions, where the action on $\operatorname{Pic}^0$ is obtained from $\mathrm{gal}$; each such datum consists of an intermediate field $\mathcal U.K$ between $\mathbb Q$ and $C$, an order homomorphism on $(\mathcal U.K)^\times$ normalised by the valuation of $r$, inertia-invariance and $n$-th root (Hensel) clauses, a period datum $\mathcal U.P$ over $D$, and a surjection $\mathcal U.eFull$ from the torus points $\mathcal U.P.TorusPoints = \operatorname{Hom}_{\mathbb Z}(\mathrm{ribbonKernel}\,D, \mathrm{Additive}\,C^\times)$ onto $\operatorname{Pic}^0$ with kernel the period lattice, together with the two $S$-equivariance clauses for the period pairing $\mathcal U.P.Q$ and for $\mathcal U.eFull$.
--
--   **Pinning.** For each level, two hypotheses tie the algebraic period datum to the analytic one. `hQ` states that for $x, y \in \Omega$ with no $H$-translate of $x$ equal to $y$, and all $\alpha, \beta \in H$, the image in $C$ of $Q(\Phi\alpha, \Phi\beta)$ times `Omega.period` of the inclusion of $H$ at $(x, y, \alpha, \beta)$ equals $1$. `hΘ` states that for $a, b, z_0 \in \Omega$ such that no $H$-translate of $a$ and no $H$-translate of $b$ equals $z_0$, every homomorphism $c : H \to C^\times$ whose values are the theta values `Omega.theta` of the inclusion of $H$ at $(a, b, z_0)$ evaluated at the translates of $z_0$, every torus point $u$ with $u(\Phi\gamma) = c(\gamma)$ for all $\gamma \in H$, and every degree-zero divisor $D_v$ equal to $\mathrm{pt}(a) - \mathrm{pt}(b)$, satisfy $\mathcal U.eFull(u) =$ the class of $D_v$.
--
--   **The arrow.** An element $g \in G$ whose image $\rho g$ is type-preserving, with `hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom`; a $C$-algebra homomorphism $\varphi : F_c \to F_d$ with `hφ` asserting that under the identifications $e_{F_c}, e_{F_d}$ the map $\varphi$ is $x \mapsto g \cdot x$ inside $\operatorname{Frac}$ of the holomorphic ring; `hφC` that $\varphi$ is integral, `hfinC` that $F_d$ is a finite $F_c$-module along $\varphi$, and `hsepC` that this extension is separable; a finite homomorphism $\mu : D_d.FiniteHom\ D_c$ of degeneracy data (maps $\mathrm{mapV}, \mathrm{mapE}$ compatible with $a$ and $b$, local degrees $\deg$, vertex degrees $\deg V$ and a total degree $\mathrm{degTotal}$, with $D_c.w(\mathrm{mapE}\,e) = \deg(e)\, D_d.w(e)$ and the three summation axioms for $\deg$ and $\deg V$); `hμV` and `hμE` asserting that $\mu.\mathrm{mapV}$ and $\mu.\mathrm{mapE}$ are, in the above coordinates, induced by $v \mapsto (\rho g)^{-1} \cdot v$ on vertex orbits and on dart orbits; and `hdeg` that $\mu.\mathrm{degTotal}$ equals the degree `finrankAlong C φ` of $F_d$ over $F_c$.
--
--   **Projection formula.** The hypothesis `hproj`: for all $x \in \mathrm{ribbonKernel}\,D_c$ and $y \in \mathrm{ribbonKernel}\,D_d$, the images in $C$ of $\mathcal U_d.P.Q(\mu.\mathrm{pullback}\,x, y)$ and of $\mathcal U_c.P.Q(x, \mu.\mathrm{pushforward}\,y)$ coincide.
--
--   **Conclusion.** For every torus point $u'$ of $\mathcal U_d.P$, every degree-zero divisor $D_1'$ on $F_d$ and every degree-zero divisor $D_1$ on $F_c$: if $\mathcal U_d.eFull(u')$ is the class of $D_1'$ in $\operatorname{Pic}^0(F_d/C)$, and if $D_1$, viewed as a divisor, equals `Divisor.pushforwardAlong φ hφC` applied to $D_1'$ (the push-forward sending a place $w$ of $F_d$ to its restriction to $F_c$ with multiplicity the residue degree), then $\mathcal U_c.eFull$ applied to the composite of $\mu.\mathrm{pullback}$ (the weighted pull-back $x \mapsto (e \mapsto \deg(e)\,x(\mu.\mathrm{mapE}\,e))$ on ribbon kernels) followed by $u'$ equals the class of $D_1$ in $\operatorname{Pic}^0(F_c/C)$.
--
--   This is one arrow of the naturality statement for Mumford–Manin–Drinfeld uniformisations of the degree-zero divisor class groups of the curves attached to two levels in a $p$-adic Schottky situation: the uniformisation of the lower level computed on pulled-back ribbon cycles represents the push-forward of a divisor class from the upper level. It is used in the construction of a natural family of equivariant uniformisations, [`AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one), and is obtained from the corresponding existence statement together with the generation of degree-zero divisors by differences of points, the algebraic closedness of the completion, and the stability of the period lattice under composition with $\mu.\mathrm{pullback}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta.lean

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

theorem AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta

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
    ∀ (u' : 𝒰d.P.TorusPoints) (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := Fd)) (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := Fc)),
      𝒰d.eFull u' = Pic0.mk D₁' →
      (D₁ : Divisor A.valuation.Completion Fc) = Divisor.pushforwardAlong φ hφC (D₁' : Divisor A.valuation.Completion Fd) →
      𝒰c.eFull (u'.comp μ.pullback) = Pic0.mk D₁ := by sorry
