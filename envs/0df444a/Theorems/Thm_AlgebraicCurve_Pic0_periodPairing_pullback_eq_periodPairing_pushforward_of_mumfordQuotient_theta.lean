-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta
-- name    : AlgebraicCurve.Pic0.periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8731bb2c-8d26-52e5-a38c-0482514685fd
-- title:
--   Adjointness of pullback and pushforward for Mumford period pairings
-- statement:
--   Throughout, $r$ is a prime, $A$ is a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime r`, i.e. the image of $r$ lies in the non-units of $A$, and $C:=$ `A.valuation.Completion` denotes the completion of $\overline{\mathbb Q}$ at the valuation of $A$.
--
--   **Arithmetic of the constant field.** A field $K_0$ with an algebra structure towards $C$ is given, together with a domain $R_0$ that is a discrete valuation ring with fraction field $K_0$ and finite residue field; the hypothesis `hR₀` states that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation at most $1$. Further, $\varpi$ is a pseudo-uniformiser of $K_0$ relative to $C$ (an element $\varpi.\varpi\in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$, such that the valuation of the image of every nonzero element of $K_0$ is squeezed between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N$), $\varpi_0$ is an irreducible element of $R_0$ with `hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ`, the hypothesis `hex` says that $\varpi$ is exhausting, i.e. every point of the Drinfeld upper half plane `Omega.upperHalfPlane K₀ C` (the complement in $C$ of the image of $K_0$) lies in one of the affinoids `Omega.affinoid ϖ n`, and `hϖr` says that the image of $\varpi.\varpi$ in $C$ and the image of $r$ in $C$ have the same valuation.
--
--   **Group acting on the tree.** A group $G$ is given with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ such that the ring `Omega.HolRingOf ϖ ρ` — the ring `Omega.holRing ϖ` of functions on the upper half plane which on each affinoid are uniform limits of uniformly bounded pole-free rational functions — is a domain. The group $\mathrm{PGL}_2(K_0)$ acts on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` (vertices: homothety classes of full $R_0$-lattices in $K_0^2$; edges from lattice adjacency) preserving adjacency, and a vertex $v_0$ is fixed.
--
--   **Level $d$.** A subgroup $\Gamma_d \le G$ is given with `htpd`, which says that $\rho(\Gamma_d)$ lies in `Mumford.typePreserving`, the subgroup of elements leaving invariant the type `vertexType` (the tree distance to `stdVertex` modulo $2$) of every vertex; $\rho(\Gamma_d)$ acts on the tree preserving adjacency, and `hfind` requires every dart of the tree to have finite stabiliser in $\rho(\Gamma_d)$. A field $F_d$ with a $C$-algebra structure is given, satisfying `IsCurveOver C F_d` (principal divisors exist and have degree zero, all residue fields of places are finite over $C$, and $\Omega_{F_d/C}$ is free of rank one), together with a $C$-algebra isomorphism $e_{F_d}$ from $F_d$ onto `Mumford.invariantFieldOf C G (HolRingOf ϖ ρ) Γd`, the subfield of $\operatorname{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$ of $\Gamma_d$-invariants. Finite types $E_d, V_d$ carry a degeneracy datum $D_d$ (maps $a, b : E_d \to V_d$ and a weight $w : E_d \to \mathbb{N}^{+}$), and bijections $e_{V_d}$ from the set `QuotVert` of $\rho(\Gamma_d)$-orbits of vertices onto $V_d$ and $e_{E_d}$ from the set of $\rho(\Gamma_d)$-orbits of darts whose chosen representative has source of type $0$ onto $E_d$; the hypotheses `hDad`, `hDbd` say that $a$ and $b$ correspond under these bijections to taking the orbit of the source, respectively the target, of a dart orbit, and `hDwd` says that the weight of an edge is the cardinality of the stabiliser in $\rho(\Gamma_d)$ of the corresponding dart. A homomorphism $\Phi_d$ from the additive group of the abelianisation of $\rho(\Gamma_d)$ into the cycle lattice `ribbonKernel Dd` (the ℤ-submodule of $E_d \to \mathbb{Z}$ annihilated by both degeneracy maps) is pinned by `hΦd`: the $e_{E_d}(e)$-coordinate of $\Phi_d$ of the class of $\gamma$ equals the value at $e$ of `Mumford.pathCycle` of the tree, the family of dart orbits, the base vertex $v_0$ and $\gamma$. Finally, a map $\mathrm{pt}_d$ from the upper half plane to the places of $F_d$ over $C$ (valuation subrings of $F_d$, proper, containing the image of $C$, and principal ideal rings) is given with: `hpt_fibd`, two points have the same image exactly when they are in the same $\rho(\Gamma_d)$-orbit; `hpt_ontod`, $\mathrm{pt}_d$ is surjective; and `hptd`, a conjunction of two clauses, namely (i) for $z$ in the upper half plane and $x \in F_d$, $x$ lies in the valuation subring of $\mathrm{pt}_d(z)$ if and only if there are $g, h$ in `HolRingOf ϖ ρ` with $h$ a non-zero-divisor, $h(z) \ne 0$, and $e_{F_d}(x) = g/h$ in $\operatorname{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$; and (ii) for such $g, h$ with $g/h$ invariant and $h(z) \ne 0$, the evaluation `Place.evalAt` of the corresponding element of $F_d$ at $\mathrm{pt}_d(z)$ equals $g(z)/h(z)$, and that element lies in the maximal ideal of the valuation subring of $\mathrm{pt}_d(z)$ if and only if $g(z) = 0$.
--
--   **Level $c$.** Data of exactly the same shape is given for a second subgroup $\Gamma_c \le G$: `htpc`, `hfinc`, a curve $F_c$ over $C$ with the isomorphism $e_{F_c}$ onto the $\Gamma_c$-invariant field, finite types $E_c, V_c$ with degeneracy datum $D_c$, bijections $e_{V_c}, e_{E_c}$ and their compatibilities `hDac`, `hDbc`, `hDwc`, a cycle map $\Phi_c$ pinned by `hΦc`, and a place parametrisation $\mathrm{pt}_c$ with `hpt_fibc`, `hpt_ontoc`, `hptc`.
--
--   **Equivariance and uniformisations.** A group $S$ is given with a homomorphism `scalar` into the decomposition subgroup of $A$ over $\mathbb{Q}$, ℤ-linear actions $\mathrm{actZ}_d$, $\mathrm{actZ}_c$ of $S$ on the cycle lattices of $D_d$, $D_c$, and homomorphisms $\mathrm{gal}_d$, $\mathrm{gal}_c$ of $S$ into the groups `SemilinearAut C F_d`, `SemilinearAut C F_c` of pairs consisting of a ring automorphism of the function field and one of $C$ compatible over the structure map. Then $\mathcal{U}_d$ and $\mathcal{U}_c$ are equivariant uniformisations `EquivariantUniformization r D_• A hA (Pic0 C F_•) S scalar actZ_• (…)`, the target group being $\mathrm{Pic}^0$ of $F_\bullet$ over $C$ (degree-zero divisors modulo principal ones) with the $S$-action obtained from $\mathrm{gal}_\bullet$ through [`DistribMulAction.toAddAut'`](def/Compat_Mathlib430.html#L196); each such datum consists of an intermediate field $\mathcal{U}.K$ of $C/\mathbb{Q}$ with an order homomorphism on its units matching the valuation to the base $v(r)$, inertia invariance and $n$-th root (Hensel) properties, a period datum $P$ with period pairing $Q$ on the cycle lattice valued in $(\mathcal{U}.K)^{\times}$ written additively, and a surjection $\mathcal{U}.\mathrm{eFull}$ from torus points onto $\mathrm{Pic}^0$ with kernel the period lattice, the pairing and the uniformisation being $S$-equivariant.
--
--   The two uniformisations are pinned to the analytic theory by four hypotheses. `hQd` states: for $x, y$ in the upper half plane with $\gamma \cdot x \neq y$ for all $\gamma \in \rho(\Gamma_d)$, and for all $\alpha, \beta \in \rho(\Gamma_d)$, the image in $C$ of $Q_d(\Phi_d(\alpha), \Phi_d(\beta))$ times the Manin–Drinfeld period `Omega.period` of the inclusion of $\rho(\Gamma_d)$ into $\mathrm{PGL}_2(K_0)$ at $x, y, \alpha, \beta$ equals $1$. `hΘd` states: for $a, b, z_0$ in the upper half plane with $z_0$ outside the $\rho(\Gamma_d)$-orbits of $a$ and of $b$, for every homomorphism $c : \rho(\Gamma_d) \to C^{\times}$ whose value at $\beta$ is the theta function `Omega.theta` with parameters $a, b, z_0$ evaluated at $\beta \cdot z_0$, for every torus point $u$ of $\mathcal{U}_d.P$ with $u(\Phi_d(\gamma)) = c(\gamma)$ for all $\gamma$, and for every degree-zero divisor $D$ on $F_d$ equal to $[\mathrm{pt}_d(a)] - [\mathrm{pt}_d(b)]$, one has $\mathcal{U}_d.\mathrm{eFull}(u) = [D]$ in $\mathrm{Pic}^0$. The hypotheses `hQc` and `hΘc` are the same statements for the level $c$ data.
--
--   **The arrow.** An element $g \in G$ is given with `hg`, saying that $\rho(g)$ is type-preserving, and `hArr`, saying $\Gamma_d \le g\Gamma_c g^{-1}$ (the image of $\Gamma_c$ under conjugation by $g$). A $C$-algebra homomorphism $\varphi : F_c \to F_d$ is given with `hφ`, saying that for every $x \in F_c$ the image of $\varphi(x)$ in $\operatorname{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$ is $g$ applied to the image of $x$; `hφC`, that $\varphi$ is integral; `hfinC`, that $F_d$ is a finite module over $F_c$ along $\varphi$; and `hsepC`, that this extension is separable. A finite homomorphism of degeneracy data $\mu : D_d \to D_c$ (maps on edges and vertices compatible with $a$ and $b$, local degrees, vertex degrees and a total degree subject to the summation identities of `DegeneracyData.FiniteHom`) is given with `hμV`: $\mu$ on vertices sends the $\rho(\Gamma_d)$-orbit of a vertex $v$ to the $\rho(\Gamma_c)$-orbit of $\rho(g)^{-1} \cdot v$; `hμE`: correspondingly on dart orbits, the edge $\mu.\mathrm{mapE}$ of an orbit $e$ has underlying $\rho(\Gamma_c)$-orbit that of $\rho(g)^{-1} \cdot e$; and `hdeg`: the total degree $\mu.\mathrm{degTotal}$ equals the degree `finrankAlong C φ` of $F_d$ over $F_c$ along $\varphi$.
--
--   **Conclusion.** For every $x$ in the cycle lattice `ribbonKernel Dc` and every $y$ in the cycle lattice `ribbonKernel Dd`, the element of $C$ underlying the period $Q_d(\mu.\mathrm{pullback}\,x,\; y)$ equals the element of $C$ underlying the period $Q_c(x,\; \mu.\mathrm{pushforward}\,y)$; here $\mu.\mathrm{pullback}$ sends a cycle $x$ to $e \mapsto \mu.\mathrm{deg}(e) \cdot x(\mu.\mathrm{mapE}(e))$, $\mu.\mathrm{pushforward}$ sums $y$ over the fibres of $\mu.\mathrm{mapE}$, and the periods, a priori units of the intermediate fields $\mathcal{U}_d.K$ and $\mathcal{U}_c.K$, are compared after their canonical inclusion into $C$.
--
--   This is the projection formula (adjointness of pullback and pushforward of cycles) for the period pairings of two Mumford–Manin–Drinfeld uniformisations of the Jacobians of quotients of the Drinfeld upper half plane, for the degeneracy morphism induced by an element $g$ conjugating one level into the other. It is used in the construction of a natural family of equivariant uniformisations of the $\mathrm{Pic}^0$ of a tower of Mumford quotients ([`AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one)), which supplies the Čerednik–Drinfeld comparison of Shimura curves with quotients of the $p$-adic upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta.lean

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

theorem AlgebraicCurve.Pic0.periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta

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
    ∀ (x : ↥(ribbonKernel Dc)) (y : ↥(ribbonKernel Dd)),
      ((((Additive.toMul (𝒰d.P.Q (μ.pullback x) y)) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) =
        ((((Additive.toMul (𝒰c.P.Q x (μ.pushforward y))) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) := by sorry
