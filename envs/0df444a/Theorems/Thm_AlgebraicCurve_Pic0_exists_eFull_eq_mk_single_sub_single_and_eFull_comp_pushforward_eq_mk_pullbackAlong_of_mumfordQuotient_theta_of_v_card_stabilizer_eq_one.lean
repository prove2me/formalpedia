-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/fadb0555-5d32-5925-ade9-5942f1813a71
-- title:
--   A theta torus point compatible with degeneracy push-forward
-- statement:
--   Throughout, $r$ is a prime, $A$ is a valuation subring of an algebraic closure of $\mathbb{Q}$ with `A.LiesOverPrime r` (that is, the image of $r$ lies in the nonunits of $A$), and $C :=$ `A.valuation.Completion` denotes the completion of the associated valued field.
--
--   **Local base data.** A field $K_0$ is given together with an algebra structure over $C$, and a domain $R_0$ which is a discrete valuation ring with fraction field $K_0$ and finite residue field. The hypothesis `hR₀` states that an element $x \in K_0$ lies in the image of $R_0$ exactly when the valuation of its image in $C$ is at most $1$. Next, $\varpi$ is a pseudo-uniformiser for $K_0$ inside $C$, i.e. an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that the valuation of the image of any nonzero element of $K_0$ is squeezed between a power of that valuation and the corresponding inverse power; $\varpi_0 \in R_0$ is irreducible (`hϖ₀`) with image $\varpi.\varpi$ in $K_0$ (`hϖ`); `hex` asserts `Omega.IsExhausted ϖ`, i.e. every point of the Drinfeld upper half plane `Omega.upperHalfPlane K₀ C` (the complement in $C$ of the image of $K_0$) lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr` asserts that the image of $\varpi.\varpi$ in $C$ has the same valuation as $r$.
--
--   **Group data.** $G$ is a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$; the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on the upper half plane (the subring of functions holomorphic on every affinoid) is assumed to be a domain, the action of $\mathrm{PGL}_2(K_0)$ on the Bruhat–Tits tree `BruhatTits.tree R₀ K₀` of homothety classes of full lattices is a graph action, and $v_0$ is a vertex of that tree.
--
--   **Data at the level $\Gamma_d$.** A subgroup $\Gamma_d \le G$ is given, with: `htpd`, the image $\rho(\Gamma_d)$ lies in the type-preserving subgroup for the standard vertex, i.e. each of its elements preserves the parity of the tree-distance from the standard vertex; a graph action of $\rho(\Gamma_d)$ on the tree; `hfind`, every dart stabiliser in $\rho(\Gamma_d)$ is finite; and `htamed`, for every vertex $w$ the image in $C$ of the order of the stabiliser of $w$ in $\rho(\Gamma_d)$ has valuation $1$.
--
--   A field $F_d$ with a $C$-algebra structure satisfying `IsCurveOver C Fd` (all divisors of nonzero elements exist and have degree $0$, all residue fields of places are finite over $C$, and the module of Kähler differentials of $F_d$ over $C$ is free of rank one) is given, together with a $C$-algebra isomorphism $e_{F_d}$ from $F_d$ onto the subfield `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γd` of $\Gamma_d$-invariants inside the fraction field of the holomorphic ring.
--
--   The combinatorial side consists of finite types $E_d$, $V_d$, a degeneracy datum $D_d$ on them (maps $a, b : E_d \to V_d$ and weights $w : E_d \to \mathbb{Z}_{>0}$), a bijection $e_{V_d}$ from the set of vertex orbits of $\rho(\Gamma_d)$ onto $V_d$, a bijection $e_{E_d}$ from the set of those dart orbits whose chosen representative has source of type $0$ onto $E_d$, and the pinning hypotheses `hDad`, `hDbd`, `hDwd`: for such an orbit $e$, $D_d.a(e_{E_d}e)$ and $D_d.b(e_{E_d}e)$ correspond under $e_{V_d}$ to the vertex orbits of the source and the target of the representative dart, and the weight $D_d.w(e_{E_d}e)$ equals the order of the stabiliser of that dart in $\rho(\Gamma_d)$. Further, $\Phi_d$ is an additive map from the additively written abelianisation of $\rho(\Gamma_d)$ to the ribbon kernel of $D_d$ (the intersection of the kernels of the joint delta maps of $D_d$ inside $E_d \to \mathbb{Z}$), and `hΦd` states that for every $\gamma$ the value of $\Phi_d$ on the class of $\gamma$, read as a function on $E_d$, is the path cycle `Mumford.pathCycle` of $\gamma$ based at $v_0$ computed along the chosen edge-orbit indexing.
--
--   Finally, $\mathrm{pt}_d$ is a map from the upper half plane to the places of $F_d$ over $C$ (valuation subrings containing $C$, distinct from the whole field, and principal ideal rings), subject to: `hpt_fibd`, $\mathrm{pt}_d(z) = \mathrm{pt}_d(z')$ if and only if $z' = \gamma z$ for some $\gamma \in \rho(\Gamma_d)$; `hpt_ontod`, $\mathrm{pt}_d$ is surjective; and `hptd`, a two-clause description of $\mathrm{pt}_d$ in analytic terms: first, $x \in F_d$ lies in the valuation subring of $\mathrm{pt}_d(z)$ exactly when $e_{F_d}(x)$ can be written as $g/h$ with $g, h$ in the holomorphic ring, $h$ a nonzerodivisor and $h(z) \ne 0$; second, for all $z$ and all such $g, h$ with $g/h$ in the invariant field and $h(z) \ne 0$, the evaluation `Place.evalAt` of the corresponding element of $F_d$ at $\mathrm{pt}_d(z)$ equals $g(z)/h(z)$, and that element lies in the nonunits of the valuation subring of $\mathrm{pt}_d(z)$ if and only if $g(z) = 0$.
--
--   **Data at the level $\Gamma_c$.** The same package is assumed verbatim for a second subgroup $\Gamma_c \le G$: `htpc`, `hfinc`, `htamec`, a field $F_c$ with `IsCurveOver C Fc` and an isomorphism $e_{F_c}$ onto the $\Gamma_c$-invariant field, finite types $E_c$, $V_c$, a degeneracy datum $D_c$, bijections $e_{V_c}$, $e_{E_c}$ pinned by `hDac`, `hDbc`, `hDwc`, a cycle map $\Phi_c$ pinned by `hΦc`, and a point-to-place map $\mathrm{pt}_c$ with `hpt_fibc`, `hpt_ontoc`, `hptc`.
--
--   **Galois data and uniformisations.** A group $S$ is given with a homomorphism `scalar` into the decomposition subgroup of $A$ over $\mathbb{Q}$, homomorphisms $\mathrm{actZ}_d$, $\mathrm{actZ}_c$ of $S$ into the $\mathbb{Z}$-linear automorphisms of the two ribbon kernels, and homomorphisms $\mathrm{gal}_d$, $\mathrm{gal}_c$ of $S$ into the semilinear automorphism groups `SemilinearAut C Fd`, `SemilinearAut C Fc` (pairs of a ring automorphism of the field and one of $C$ compatible with the structure map). Then $\mathcal{U}_d$ is an `EquivariantUniformization` for $r$, $D_d$, $A$, $hA$, the group $\mathrm{Pic}^0(F_d/C)$ (degree-zero divisors modulo principal ones), $S$, `scalar`, $\mathrm{actZ}_d$ and the additive action of $S$ on $\mathrm{Pic}^0$ induced by $\mathrm{gal}_d$: that is, an intermediate field $K \subseteq C$ over $\mathbb{Q}$ with an order homomorphism on its units compatible with valuations, inertia-invariance and an $n$-th root (Hensel) property, a period datum $P$ for $D_d$ over $K$ and $C$, and a surjective additive map `eFull` from the torus points $P.\mathrm{TorusPoints}$ (the $\mathbb{Z}$-linear maps from the ribbon kernel to $\mathrm{Additive}\,C^{\times}$) onto $\mathrm{Pic}^0(F_d/C)$ whose kernel is exactly the period lattice, together with the $S$-equivariance of the period pairing $Q$ and of `eFull`. Similarly $\mathcal{U}_c$ for $D_c$ and $\mathrm{Pic}^0(F_c/C)$.
--
--   **Analytic pinning of the two uniformisations.** `hQd` states that for all $x, y$ in the upper half plane such that $\gamma x \ne y$ for every $\gamma \in \rho(\Gamma_d)$, and all $\alpha, \beta \in \rho(\Gamma_d)$, the image in $C$ of the period $\mathcal{U}_d.P.Q(\Phi_d\alpha, \Phi_d\beta)$ multiplied by the analytic period `Omega.period` of the inclusion of $\rho(\Gamma_d)$ into $\mathrm{PGL}_2(K_0)$ at $(x, y, \alpha, \beta)$ — namely the theta product $\theta(x, \alpha x, y)$ evaluated at $\beta y$ — equals $1$. `hΘd` states that for all $a, b, z_0$ in the upper half plane with $\gamma a \ne z_0$ and $\gamma b \ne z_0$ for all $\gamma \in \rho(\Gamma_d)$, every homomorphism $c : \rho(\Gamma_d) \to C^{\times}$ with $c(\beta) = \theta(a, b, z_0)(\beta z_0)$ for all $\beta$, every torus point $u$ of $\mathcal{U}_d.P$ with $u(\Phi_d\gamma) = c(\gamma)$ for all $\gamma$, and every degree-zero divisor $Dv$ whose underlying divisor is $\mathrm{pt}_d(a) - \mathrm{pt}_d(b)$, one has $\mathcal{U}_d.\mathrm{eFull}(u) = [Dv]$ in $\mathrm{Pic}^0(F_d/C)$. The hypotheses `hQc`, `hΘc` are the same statements for $\Gamma_c$, $\Phi_c$, $\mathrm{pt}_c$ and $\mathcal{U}_c$.
--
--   **The arrow.** An element $g \in G$ is given with `hg`: $\rho(g)$ type-preserving, and `hArr`: $\Gamma_d \le g\Gamma_c g^{-1}$ (the image of $\Gamma_c$ under conjugation by $g$). Further, $\varphi : F_c \to F_d$ is a $C$-algebra homomorphism with `hφ`: for every $x \in F_c$, $e_{F_d}(\varphi x)$ equals the translate by $g$ of $e_{F_c}(x)$ inside the fraction field of the holomorphic ring; `hφC`: the underlying ring homomorphism is integral; `hfinC`: $F_d$ is a finite module over $F_c$ along $\varphi$; `hsepC`: this extension is separable. On the combinatorial side, $\mu$ is a finite homomorphism $D_d \to D_c$ of degeneracy data (vertex and edge maps commuting with $a$ and $b$, local degrees $\mathrm{deg}$ on edges, $\mathrm{degV}$ on vertices and a total degree $\mathrm{degTotal}$, with $D_c.w \circ \mu.\mathrm{mapE} = \mathrm{deg}\cdot D_d.w$ and the fibrewise degree-summation identities), pinned by `hμV`: $\mu.\mathrm{mapV}$ sends the $\rho(\Gamma_d)$-orbit of a vertex $v$ to the $\rho(\Gamma_c)$-orbit of $\rho(g)^{-1}v$; `hμE`: for a type-$0$ edge orbit $e$, the dart orbit corresponding to $\mu.\mathrm{mapE}(e_{E_d}e)$ is the $\rho(\Gamma_c)$-orbit of $\rho(g)^{-1}$ applied to the representative dart of $e$; and `hdeg`: $\mu.\mathrm{degTotal}$ equals the degree `finrankAlong C φ` of $F_d$ over $F_c$ along $\varphi$.
--
--   **Conclusion.** For all points $a, b$ of the upper half plane, every degree-zero divisor $Dv$ on $F_c$ and every degree-zero divisor $Dv'$ on $F_d$ such that the underlying divisor of $Dv$ is $\mathrm{pt}_c(a) - \mathrm{pt}_c(b)$ and the underlying divisor of $Dv'$ is the pullback `Divisor.pullbackAlong φ hφC` of that of $Dv$, there exists a torus point $w_0$ of $\mathcal{U}_c.P$ such that
--
--   $$\mathcal{U}_c.\mathrm{eFull}(w_0) = [Dv] \quad\text{and}\quad \mathcal{U}_d.\mathrm{eFull}(w_0 \circ \mu.\mathrm{pushforward}) = [Dv'],$$
--
--   where $\mu.\mathrm{pushforward}$ is the $\mathbb{Z}$-linear map from the ribbon kernel of $D_d$ to that of $D_c$ induced by $\mu.\mathrm{mapE}$, so that $w_0 \circ \mu.\mathrm{pushforward}$ is a torus point of $\mathcal{U}_d.P$.
--
--   This is the analytic core of the conorm square for a degeneracy map between two Mumford quotients of the Drinfeld upper half plane: the torus point produced is the theta multiplier of $\rho(\Gamma_c)$ attached to the pair $a, b$, and the second identity says that composing it with the push-forward of cycles computes the class of the pulled-back divisor on the finer level. It is cited by [`AlgebraicCurve.Pic0.eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one), where the existential torus point is identified with a prescribed one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one.lean

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

theorem AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one

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
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ) :
    ∀ (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fc))
      (Dv' : Divisor.degZero (K := A.valuation.Completion) (F := Fd)),
      (Dv : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc a) 1 - Finsupp.single (ptc b) 1 →
      (Dv' : Divisor A.valuation.Completion Fd) = Divisor.pullbackAlong φ hφC (Dv : Divisor A.valuation.Completion Fc) →
      ∃ w₀ : 𝒰c.P.TorusPoints, 𝒰c.eFull w₀ = Pic0.mk Dv ∧ 𝒰d.eFull (w₀.comp μ.pushforward) = Pic0.mk Dv' := by sorry
