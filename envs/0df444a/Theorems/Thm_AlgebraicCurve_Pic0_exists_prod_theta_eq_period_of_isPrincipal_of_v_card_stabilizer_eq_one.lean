-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/a2ba6c24-6bc4-5b11-aa5b-de8717af7288
-- title:
--   Principal theta divisors on a Mumford quotient are periods
-- statement:
--   Throughout, $r$ is a prime number and $A$ is a valuation subring of $\overline{\mathbb Q}$ with $(r:\overline{\mathbb Q})$ a non-unit of $A$ (the hypothesis `hA`, i.e. $A$ lies over $r$); $C$ denotes the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ at the valuation of $A$.
--
--   **Galois bookkeeping.** $S$ is a group equipped with homomorphisms `scalar : S → A.decompositionSubgroup ℚ` and `ι` in the opposite direction with `scalar ∘ ι` the identity (`hι`).
--
--   **The local field and its upper half plane.** $K_0$ is a field with a $C$-algebra structure, $R_0$ a discrete valuation domain with fraction field $K_0$ and finite residue field, and `hR₀` requires that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation $\le 1$. Next, $\varpi$ is a pseudo-uniformiser of $K_0$ relative to $C$, that is an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that the valuation of any non-zero element of $K_0$ is squeezed between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N$; $\varpi_0 \in R_0$ is irreducible with $\varpi_0 \mapsto \varpi.\varpi$ (`hϖ₀`, `hϖ`); `hex` asserts that $\varpi$ is exhausted, i.e. every point of the Drinfeld upper half plane $\Omega = C \setminus \mathrm{im}(K_0 \to C)$ lies in one of the affinoids `Omega.affinoid ϖ n`; and `hϖr` asserts $v(\varpi.\varpi) = v(r)$ in $C$.
--
--   **The group and the tree.** $G$ is a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism; the ring `Omega.HolRingOf ϖ ρ` of holomorphic functions on $\Omega$ (functions that on each affinoid are uniform limits of uniformly bounded, pole-free rational functions) is assumed to be a domain, and $\mathrm{PGL}_2(K_0)$ is assumed to act on the Bruhat–Tits tree of $(R_0,K_0)$ through graph automorphisms. $\Gamma \le G$ is a subgroup whose image $\rho(\Gamma)$ consists of type-preserving automorphisms, i.e. preserves the parity of the distance to the standard vertex (`htp`); $\rho(\Gamma)$ also acts through graph automorphisms; all dart stabilisers in $\rho(\Gamma)$ are finite (`hfin`); and tameness is imposed by `htame`: for every vertex $w$ the image in $C$ of $\#\mathrm{Stab}_{\rho(\Gamma)}(w)$ has valuation $1$.
--
--   **The quotient curve.** $FC$ is a field, an algebra over $C$ which `IsCurveOver C FC` makes a curve over $C$: every non-zero element has a divisor of degree zero recording its orders at all places, every place has residue field finite over $C$, and $\Omega_{FC/C}$ is free of rank one. The map `eFC` is a $C$-algebra isomorphism of $FC$ with the subfield of $\mathrm{Frac}(\mathrm{HolRingOf}\ \varpi\ \rho)$ of elements fixed by every element of $\Gamma$, and `hfg` requires some $x \in FC$ transcendental over $C$ with $FC$ finite over $C(x)$.
--
--   **Combinatorial data.** $E$ and $V$ are finite types and $D$ is a `DegeneracyData E V`, i.e. two maps $D.a, D.b : E \to V$ and widths $D.w : E \to \mathbb N^{+}$. The bijection $e_V$ identifies the set of $\rho(\Gamma)$-orbits of vertices with $V$, and $e_E$ identifies with $E$ the set of those $\rho(\Gamma)$-orbits of darts whose chosen representative has source of type $0$. The hypotheses `hDa`, `hDb`, `hDw` say that for each such orbit $e$, $D.a(e_E e)$ and $D.b(e_E e)$ are the vertex orbits of the source and the target of the representative dart, and $D.w(e_E e)$ is the order of the stabiliser of that dart in $\rho(\Gamma)$. Further, $v_0$ is a vertex and $\Phi$ an additive homomorphism from the additive group of the abelianisation of $\rho(\Gamma)$ to `ribbonKernel D`, the submodule of $E \to \mathbb Z$ cut out by the two pushforward maps along $D.a$ and $D.b$; `hΦ` requires that the $e$-coordinate of $\Phi(\gamma)$ equals `Mumford.pathCycle`, the signed crossing number of the orbit of $e$ by a chosen path from $v_0$ to $\gamma v_0$.
--
--   **Places from points of $\Omega$.** The map $pt$ sends a point of $\Omega$ to a place of $FC$ over $C$ (a valuation subring of $FC$, proper, containing the image of $C$, and a principal ideal ring). The hypothesis `hpt_fib` states that $pt(z) = pt(z')$ holds exactly when $z'$ lies in the $\rho(\Gamma)$-orbit of $z$, and `hpt_onto` that $pt$ is surjective. The two-part hypothesis `hpt` identifies $pt(z)$ with evaluation at $z$: $x \in FC$ lies in the valuation subring of $pt(z)$ precisely when `eFC x` can be written as $g/h$ with $g, h$ holomorphic, $h$ a non-zero-divisor and $h(z) \neq 0$; and, for any such representation of an element of the invariant field with $h(z) \neq 0$, the value `(pt z).evalAt` of the corresponding element of $FC$ is $g(z)/h(z)$, this element lying in the maximal ideal of the valuation subring exactly when $g(z) = 0$.
--
--   **Equivariance.** `galFC` is a homomorphism from $S$ to the group of semilinear automorphisms of $FC$ over $C$, i.e. pairs of a ring automorphism of $FC$ and one of $C$ intertwined by the structure map; `hgalFC_base` says the $C$-component of `galFC σ` acts as `scalar σ`. By `hgal`, each $\sigma \in S$ acts on the invariant field, through `eFC`, as $n \cdot$ (the automorphism of $\mathrm{Frac}(\mathrm{HolRingOf}\ \varpi\ \rho)$ induced by an isometric automorphism $t$ of $C$ fixing $K_0$ pointwise and preserving valuations), for some $n$ in the normaliser of $\Gamma$ in $G$. The homomorphisms $\pi_V : S \to \mathrm{Perm}(V)$, $\pi_E : S \to \mathrm{Perm}(E)$ and $\mathrm{sgn} : S \to \mathbb Z^{\times}$ are required (`hπV`, `hπE`) to be compatible with any such pair $(n,t)$ representing $\sigma$: $\pi_V(\sigma)$ sends the orbit of a vertex $v$ to the orbit of $\rho(n)v$; and on edges, if $\rho(n)$ is type-preserving then $\mathrm{sgn}(\sigma) = 1$ and $\pi_E(\sigma)$ sends the orbit of a dart to the orbit of its image under $\rho(n)$, while if $\rho(n)$ is not type-preserving then $\mathrm{sgn}(\sigma) = -1$ and the image orbit is that of the reversed dart. Moreover $\pi_E$ preserves the widths $D.w$ (`hπ_width`); when $\mathrm{sgn}(\sigma) = 1$ the permutations $\pi_E, \pi_V$ commute with $D.a$ and with $D.b$ (`hsgn_pos`), and when $\mathrm{sgn}(\sigma) = -1$ they interchange them (`hsgn_neg`); by `hπ_inertia`, if $\tau$ in the decomposition group has underlying field automorphism in the inertia subgroup then $\pi_V(\iota\tau)$, $\pi_E(\iota\tau)$ and $\mathrm{sgn}(\iota\tau)$ are trivial. Finally `actZ` is an action of $S$ by $\mathbb Z$-linear automorphisms of `ribbonKernel D` with $(\mathrm{actZ}\,\sigma\, x)(\pi_E(\sigma)e) = \mathrm{sgn}(\sigma)\, x(e)$ (`hactZ`).
--
--   **The divisor.** Finally $n \in \mathbb N$ and $a, b, z : \mathrm{Fin}\,n \to C$ are families of points of $\Omega$ (`ha`, `hb`, `hz`) such that no $\rho(\Gamma)$-translate of $a_i$ or of $b_i$ equals $z_i$ (`hza`, `hzb`), and `hprin` asserts that the divisor $\sum_i \bigl( [pt(a_i)] - [pt(b_i)] \bigr)$ on $FC$ is principal, i.e. there is a non-zero $f \in FC$ whose order at every place of $FC$ over $C$ is the coefficient of that place in this divisor.
--
--   **Conclusion.** There exist $x, y \in C$ such that: $x$ lies in $\Omega$; $y$ lies in $\Omega$; for every $\gamma \in \rho(\Gamma)$ the Möbius image of $x$ under $\gamma$ is different from $y$; and there exists $\alpha \in \rho(\Gamma)$ such that for every $\beta \in \rho(\Gamma)$
--   $$\prod_{i} \Theta_{a_i,b_i}^{z_i}\bigl(\beta z_i\bigr) = \Theta^{y}_{x,\alpha x}\bigl(\beta y\bigr),$$
--   where the theta functions are formed for the inclusion $\rho(\Gamma) \hookrightarrow \mathrm{PGL}_2(K_0)$: $\Theta_{a,b}^{z_0}(z)$ is the multipliable product over $\gamma \in \rho(\Gamma)$ of the cross-ratios of $z, z_0, \gamma a, \gamma b$, and the right-hand side is `Omega.period` of $x$ with base point $y$ at $(\alpha,\beta)$, namely $\Theta_{x,\alpha x}^{y}(\beta y)$.
--
--   This is Abel's theorem for a Mumford curve in the tame case: on the quotient of the Drinfeld upper half plane by $\rho(\Gamma)$, a divisor $\sum_i([pt\,a_i]-[pt\,b_i])$ is principal only if the corresponding product of theta multipliers is a row of the period pairing of $\rho(\Gamma)$. It feeds the comparison of the quotient curve with the torus uniformisation built from the degeneracy data $D$, being cited by [`AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one), where it yields the inclusion of the kernel of the uniformisation map in the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.lean

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
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one

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
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (n : ℕ) (a b z : Fin n → A.valuation.Completion)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hza : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i) (hzb : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (hprin : Divisor.IsPrincipal (K := A.valuation.Completion) (F := FC)
      (∑ i, (Finsupp.single (pt ⟨a i, ha i⟩) 1 - Finsupp.single (pt ⟨b i, hb i⟩) 1) : Divisor A.valuation.Completion FC)) :
    ∃ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧
      (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) ∧
      ∃ α : ↥(Γ.map ρ), ∀ β : ↥(Γ.map ρ),
        ∏ i, Omega.theta (Γ.map ρ).subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z i)) =
          Omega.period (Γ.map ρ).subtype x y α β := by sorry
