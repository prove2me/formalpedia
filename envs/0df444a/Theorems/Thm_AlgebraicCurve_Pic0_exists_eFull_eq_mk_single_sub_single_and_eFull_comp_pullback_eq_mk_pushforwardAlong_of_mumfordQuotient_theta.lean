-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
-- name    : AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bed8955a-6e3c-54aa-aa97-b3b30c1bbd52
-- title:
--   Theta torus point lifting a two-point divisor and its push-forward
-- statement:
--   Throughout write $C :=$ `A.valuation.Completion` for the completion of the valued field attached to the valuation subring $A$ of $\overline{\mathbb{Q}}$, $\Omega :=$ `Omega.upperHalfPlane K₀ C` for the complement in $C$ of the image of $K_0$, and $\mathcal{T} :=$ `BruhatTits.tree R₀ K₀` for the graph on homothety classes of full lattices obtained from the adjacency relation `VertRel`.
--
--   **Base data.** A prime $r$; a valuation subring $A$ of `AlgebraicClosure ℚ` together with `hA : A.LiesOverPrime r`, i.e. $r$ lies in the non-units of $A$; a field $K_0$ which is an algebra over $C$; a discrete valuation ring $R_0$ with finite residue field, an algebra over which $K_0$ is the fraction field; the hypothesis `hR₀` that an element of $K_0$ comes from $R_0$ exactly when its image in $C$ has valuation $\le 1$; a pseudo-uniformiser $\varpi$ of $K_0$ relative to $C$ (an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$, together with the scaling condition of `Omega.PseudoUniformizer`); an irreducible $\varpi_0 \in R_0$ with $\varpi_0 \mapsto \varpi.\varpi$ (`hϖ₀`, `hϖ`); the hypothesis `hex` that $\varpi$ is exhausted, i.e. every point of $\Omega$ lies in some affinoid `Omega.affinoid ϖ n`; and `hϖr`, that the images of $\varpi.\varpi$ and of $r$ in $C$ have the same valuation. Further, a group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring `Omega.HolRingOf ϖ ρ` (a copy of the ring `Omega.holRing ϖ` of functions on $\Omega$ holomorphic on every affinoid) is a domain, and a vertex $v_0$ of the lattice tree.
--
--   The data then come in two parallel blocks, indexed by $d$ and $c$; the two blocks are identical in shape and are described once.
--
--   **Level data ($\Gamma_d$, resp. $\Gamma_c$).** A subgroup $\Gamma_d \le G$ with `htpd` asserting that $\rho(\Gamma_d)$ is contained in `Mumford.typePreserving`, the subgroup of elements preserving the parity `vertexType` of the distance in $\mathcal{T}$ to the standard vertex, $\mathcal{T}$ carrying an action of $\rho(\Gamma_d)$ by graph automorphisms; and `hfind`, that every dart of $\mathcal{T}$ has finite stabiliser in $\rho(\Gamma_d)$.
--
--   **Curve data.** A field $F_d$, an algebra over $C$, which `IsCurveOver C F_d`, i.e. every non-zero element of $F_d$ has a degree-zero principal divisor, every place of $F_d$ over $C$ has residue field finite over $C$, and $\Omega[F_d/C]$ is free of rank one; together with a $C$-algebra isomorphism $e_{F_d}$ from $F_d$ onto the invariant subfield `Mumford.invariantFieldOf C G (HolRingOf ϖ ρ) Γd` of the fraction field of the ring of holomorphic functions.
--
--   **Combinatorial data.** Finite types $E_d$, $V_d$; a degeneracy datum $D_d$ on them (maps $a, b : E_d \to V_d$ and a weight $w : E_d \to \mathbb{N}^{+}$); an equivalence $e_{V_d}$ between the set of $\rho(\Gamma_d)$-orbits of vertices and $V_d$; an equivalence $e_{E_d}$ between $E_d$ and the set of those $\rho(\Gamma_d)$-orbits of darts whose chosen representative has source of vertex type $0$; and the pinning hypotheses `hDad`, `hDbd`, `hDwd`: $a$ and $b$ correspond under these equivalences to the source and target vertex-orbit of the chosen dart representative, and $w$ of an edge equals the cardinality of the stabiliser in $\rho(\Gamma_d)$ of that dart representative.
--
--   **Cycle map.** An additive map $\Phi_d$ from the additive group of the abelianisation of $\rho(\Gamma_d)$ to `ribbonKernel Dd`, the $\mathbb{Z}$-submodule of functions $E_d \to \mathbb{Z}$ given by the intersection of the kernels of the maps `jointDelta Dd i`; and `hΦd`, that for each $\gamma$ the coordinate of $\Phi_d(\gamma)$ at an edge is the value at that edge of `Mumford.pathCycle`, the cycle of a chosen path from $v_0$ to $\gamma \cdot v_0$.
--
--   **Points map.** A map $\mathrm{pt}_d$ from $\Omega$ to places of $F_d$ over $C$ (valuation subrings of $F_d$ containing $C$, distinct from $F_d$ and principal ideal rings), with `hpt_fibd`: $\mathrm{pt}_d(z) = \mathrm{pt}_d(z')$ if and only if $z' = \gamma \cdot z$ for some $\gamma \in \rho(\Gamma_d)$; `hpt_ontod`: $\mathrm{pt}_d$ is surjective; and `hptd`, a conjunction of two clauses: first, $x \in F_d$ lies in the valuation subring of $\mathrm{pt}_d(z)$ exactly when $e_{F_d}(x)$ is, in the fraction field, of the form `Localization.mk g ⟨h, hh⟩` with $h$ a non-zero-divisor of the holomorphic ring and $h(z) \neq 0$; second, for such $g, h$ with $\mathrm{mk}\,g\,h$ in the invariant field and $h(z) \neq 0$, the evaluation of the corresponding element of $F_d$ at $\mathrm{pt}_d(z)$ is $g(z)/h(z)$, and that element lies in the non-units of the valuation subring of $\mathrm{pt}_d(z)$ if and only if $g(z) = 0$.
--
--   **Equivariance and uniformisations.** A group $S$ with a homomorphism `scalar` to the decomposition subgroup of $A$ over $\mathbb{Q}$, homomorphisms $\mathrm{actZ}_d$, $\mathrm{actZ}_c$ from $S$ to the $\mathbb{Z}$-linear automorphism groups of `ribbonKernel Dd`, `ribbonKernel Dc`, and homomorphisms $\mathrm{gal}_d$, $\mathrm{gal}_c$ from $S$ to the semilinear automorphism groups `SemilinearAut C Fd`, `SemilinearAut C Fc` (pairs of ring automorphisms of the function field and of $C$ compatible with the structure map). Then equivariant uniformisations $\mathcal{U}_d$ and $\mathcal{U}_c$, in the sense of `EquivariantUniformization r Dd A hA (Pic0 C Fd) S scalar actZd …` and its $c$-analogue, the $S$-action on $\mathrm{Pic}^0$ being that induced by $\mathrm{gal}_d$, resp. $\mathrm{gal}_c$; each such datum consists of an intermediate field $K \subset C$ over $\mathbb{Q}$ with an order homomorphism compatible with the valuation and with inertia- and Hensel-type properties, a period datum $P$ with period pairing $Q$, and a surjective additive map $\mathrm{eFull}$ from the torus points $P.\mathrm{TorusPoints} = \mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}, \mathrm{Additive}\,C^{\times})$ onto $\mathrm{Pic}^0$ with kernel the period lattice, equivariant for $S$.
--
--   **Analytic pinning.** The hypothesis `hQd`: for all $x, y \in \Omega$ such that no $\gamma \in \rho(\Gamma_d)$ carries $x$ to $y$ under `Omega.pmoebius`, and all $\alpha, \beta \in \rho(\Gamma_d)$, the image in $C$ of $\mathcal{U}_d.P.Q(\Phi_d(\alpha), \Phi_d(\beta))$ times the analytic period `Omega.period` of $\rho(\Gamma_d)$ at $(x, y)$ for $(\alpha, \beta)$ equals $1$. The hypothesis `hΘd`: for all $a, b, z_0 \in \Omega$ such that $z_0$ is in neither the $\rho(\Gamma_d)$-orbit of $a$ nor that of $b$, for every homomorphism $c : \rho(\Gamma_d) \to C^{\times}$ whose value at $\beta$ is $\Theta(a, b, z_0; \beta \cdot z_0)$ (the theta product `Omega.theta` for $\rho(\Gamma_d)$), for every torus point $u$ of $\mathcal{U}_d.P$ with $u(\Phi_d(\gamma)) = c(\gamma)$ for all $\gamma$, and for every degree-zero divisor $Dv$ whose underlying divisor is $\mathrm{pt}_d(a) - \mathrm{pt}_d(b)$, one has $\mathcal{U}_d.\mathrm{eFull}\,u = [Dv]$ in $\mathrm{Pic}^0(F_d)$. The hypotheses `hQc`, `hΘc` are the same statements for the $c$-block.
--
--   **The arrow.** An element $g \in G$ with `hg` asserting that $\rho(g)$ is type-preserving, and `hArr` asserting $\Gamma_d \le g\Gamma_c g^{-1}$; a $C$-algebra map $\varphi : F_c \to F_d$ with `hφ`, that $e_{F_d}(\varphi(x))$ equals $g \cdot e_{F_c}(x)$ inside the fraction field of the holomorphic ring; `hφC`, that $\varphi$ is integral; `hfinC` and `hsepC`, that $F_d$ is finite, respectively separable, over $F_c$ along $\varphi$; a finite morphism $\mu : D_d \to D_c$ of degeneracy data (maps on vertices and edges compatible with $a$ and $b$, edge degrees, vertex degrees and a total degree, subject to the weight and degree-sum identities of `DegeneracyData.FiniteHom`); the pinnings `hμV` and `hμE`, that $\mu$ on vertex-orbits and on edge-orbits is induced by $v \mapsto \rho(g)^{-1} \cdot v$; and `hdeg`, that the total degree of $\mu$ equals the degree `finrankAlong C φ` of $F_d$ over $F_c$.
--
--   **Conclusion.** For all $a, b \in \Omega$, every degree-zero divisor $Dv$ on $F_d$ and every degree-zero divisor $Dv'$ on $F_c$ such that the underlying divisor of $Dv$ is $\mathrm{pt}_d(a) - \mathrm{pt}_d(b)$ and the underlying divisor of $Dv'$ is `Divisor.pushforwardAlong φ hφC` applied to that of $Dv$, there exists a torus point $w_0$ of $\mathcal{U}_d.P$, i.e. a $\mathbb{Z}$-linear map from `ribbonKernel Dd` to $\mathrm{Additive}\,C^{\times}$, such that
--
--   $$\mathcal{U}_d.\mathrm{eFull}\,w_0 = [Dv] \quad\text{and}\quad \mathcal{U}_c.\mathrm{eFull}\,(w_0 \circ \mu.\mathrm{pullback}) = [Dv'],$$
--
--   where $\mu.\mathrm{pullback} : \mathrm{ribbonKernel}\,D_c \to \mathrm{ribbonKernel}\,D_d$ sends $y$ to $e \mapsto \mu.\mathrm{deg}(e)\cdot y(\mu.\mathrm{mapE}(e))$, and $[\cdot]$ denotes the class `Pic0.mk` of a degree-zero divisor.
--
--   This is the analytic step, via theta functions and their multipliers, in the comparison of two Mumford uniformisations attached to two levels of the same group acting on Drinfeld's upper half plane: it produces a torus point representing the class of a difference of two points of the first curve, and shows that its composite with the pull-back on ribbon cycles represents the push-forward class on the second curve. It is the input to [`AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta`](thm.html#AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta), in the comparison of Hecke-type correspondences on Čerednik–Drinfeld uniformised curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta.lean

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
open CerednikDrinfeld AlgebraicCurve ModularCurve
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta

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
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ) :
    ∀ (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd))
      (Dv' : Divisor.degZero (K := A.valuation.Completion) (F := Fc)),
      (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd a) 1 - Finsupp.single (ptd b) 1 →
      (Dv' : Divisor A.valuation.Completion Fc) = Divisor.pushforwardAlong φ hφC (Dv : Divisor A.valuation.Completion Fd) →
      ∃ w₀ : 𝒰d.P.TorusPoints, 𝒰d.eFull w₀ = Pic0.mk Dv ∧ 𝒰c.eFull (w₀.comp μ.pullback) = Pic0.mk Dv' := by sorry
