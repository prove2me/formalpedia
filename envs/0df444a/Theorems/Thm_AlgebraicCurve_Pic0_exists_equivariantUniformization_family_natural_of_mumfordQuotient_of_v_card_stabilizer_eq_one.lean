-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one
-- name    : AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/01178304-6808-525a-835b-bf24bb0a153f
-- title:
--   Natural equivariant uniformisation of Jacobians of Mumford quotients
-- statement:
--   Throughout, write $C$ for `A.valuation.Completion`, $\mathcal T$ for `BruhatTits.tree R₀ K₀` (the graph on homothety classes of full lattices in $K_0^2$ with adjacency `VertRel`), and $x_0$ for [`LT.LatticeTree.stdVertex R₀ K₀`](def/LatticeTreeOrbital.html#L358).
--
--   **Global data.** A prime $r$; a valuation subring $A$ of `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime r`, i.e. $r$ lies in `A.nonunits`; a group $S$ together with homomorphisms `scalar : S →* A.decompositionSubgroup ℚ` and `ι` in the opposite direction satisfying `hι : scalar (ι τ) = τ` for all $\tau$, so that $S$ maps onto the decomposition group with a distinguished homomorphic section.
--
--   **Local data (group `hR₀`, `hϖ₀`, `hϖ`, `hex`, `hϖr`).** A field $K_0$ with an algebra structure on $C$; a discrete valuation domain $R_0$ with fraction field $K_0$ and finite residue field; `hR₀` says that an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation $\le 1$. Further, a pseudo-uniformiser `ϖ : Omega.PseudoUniformizer K₀ C`, that is an element $\varpi =$ `ϖ.ϖ` of $K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that for every nonzero $a \in K_0$ there is $N$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$; an irreducible $\varpi_0 \in R_0$ with `algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ`; the exhaustion hypothesis `hex : Omega.IsExhausted ϖ`, that every point of the upper half-plane `Omega.upperHalfPlane K₀ C` lies in some affinoid `Omega.affinoid ϖ n`; and `hϖr`, that the image of $\varpi$ in $C$ has the same valuation as $r$.
--
--   **The acting group.** A group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}(2,K_0)$; the ring `Omega.HolRingOf ϖ ρ` (the subring of functions on the upper half-plane holomorphic on every affinoid `affinoid ϖ n`, viewed with its $G$-action through $\rho$) is assumed to be a domain; $\mathrm{PGL}(2,K_0)$ acts on $\mathcal T$ preserving adjacency (`Mumford.GraphAction`), and membership in `Mumford.typePreserving PGL(2, K₀) 𝒯 x₀` — the subgroup of elements $g$ with `vertexType 𝒯 x₀ (g • w) = vertexType 𝒯 x₀ w` for all vertices $w$, where `vertexType` is the graph distance from $x_0$ read modulo $2$ — is decidable.
--
--   **The objects, indexed by $j \in J$.** Subgroups $\Gamma_j \le G$ such that (`htp`) the image $\rho(\Gamma_j)$ is type-preserving with respect to $x_0$, acting on $\mathcal T$ preserving adjacency, with (`hfin`) all dart stabilisers in $\rho(\Gamma_j)$ finite and (`htame`) every vertex stabiliser tame in the sense that `Valued.v ((Nat.card (stabilizer (ρ(Γ j)) w) : ℕ) : C) = 1`.
--
--   For each $j$, a field $FC_j$ which is a $C$-algebra satisfying `IsCurveOver C (FC j)` (principal divisors of degree zero exist for all nonzero functions, every place has residue field finite over $C$, and $\Omega_{FC_j/C}$ is free of rank one), an isomorphism of $C$-algebras `eFC j : FC j ≃ₐ[C] Mumford.invariantFieldOf C G (HolRingOf ϖ ρ) (Γ j)` onto the subfield of $\Gamma_j$-invariants inside $\operatorname{Frac}$ of the holomorphic ring, and `hfg j`: some $x \in FC_j$ is transcendental over $C$ with $FC_j$ finite over $C(x)$.
--
--   **The combinatorial data.** Finite types $E_j$, $V_j$ with decidable equality, a degeneracy datum $D_j$ (two maps $a, b : E_j \to V_j$ and widths $w : E_j \to \mathbb N_{>0}$), a bijection `eV j` from the set of $\rho(\Gamma_j)$-orbits of vertices of $\mathcal T$ to $V_j$, and a bijection `eE j` from the set of those $\rho(\Gamma_j)$-orbits of darts whose chosen representative has origin of vertex type $0$ onto $E_j$. The hypotheses `hDa`, `hDb` identify $a$ and $b$ with the orbit of the origin, respectively terminus, of the representative dart, and `hDw` identifies the width of an edge with the cardinality of the stabiliser of that dart.
--
--   **The semilinear Galois data.** For each $j$, a homomorphism `galFC j : S →* SemilinearAut C (FC j)`, where `SemilinearAut C (FC j)` is the group of pairs consisting of a ring automorphism of $FC_j$ and one of $C$ compatible with `algebraMap`; `hgalFC_base` requires the base component of `galFC j σ` to be the action of `scalar σ` on $C$. The hypothesis `hgal` requires, for each $j$ and $\sigma$, the existence of $n$ in the normaliser of $\Gamma_j$ in $G$ and of an isometric automorphism $t$ of $C$ over $K_0$ (`Omega.IsometricAut K₀ C`) such that, read inside $\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi\ \rho)$ through `eFC j`, the action of `galFC j σ` is the composite of the ambient semilinear automorphism `Omega.toAmbientOf ϖ ρ t` with multiplication by $n$.
--
--   **The combinatorial $S$-action (group `hπV`, `hπE`, `hπ_width`, `hsgn_pos`, `hsgn_neg`, `hπ_inertia`, `hactZ`).** Homomorphisms `πV j : S →* Equiv.Perm (V j)`, `πE j : S →* Equiv.Perm (E j)` and `sgn : S →* ℤˣ` such that: whenever $n$ in the normaliser of $\Gamma_j$ and $t$ represent `galFC j σ` in the sense of the formula in `hgal`, then `πV j σ` is, under `eV j`, the map induced by $v \mapsto \rho(n) \cdot v$ (`hπV`), and for every type-$0$ dart orbit $e$ (`hπE`): if $\rho(n)$ is type-preserving then `sgn σ = 1` and `πE j σ e` corresponds to the orbit of $\rho(n) \cdot e$, while if $\rho(n)$ is not type-preserving then `sgn σ = -1` and `πE j σ e` corresponds to the orbit of the reversed dart $(\rho(n) \cdot e)^{\mathrm{symm}}$. Widths are $\pi_E$-invariant (`hπ_width`); when `sgn σ = 1` the maps $a, b$ are $S$-equivariant and when `sgn σ = -1` they are interchanged (`hsgn_pos`, `hsgn_neg`); and (`hπ_inertia`) for $\tau$ in the decomposition group whose underlying automorphism of $\overline{\mathbb Q}$ lies in `A.inertiaSubgroupIn ℚ` one has `πV j (ι τ) = 1`, `πE j (ι τ) = 1` and `sgn (ι τ) = 1`. Finally homomorphisms `actZ j : S →* (ribbonKernel (D j) ≃ₗ[ℤ] ribbonKernel (D j))` — where `ribbonKernel (D j)` is the submodule of $\mathbb Z$-valued functions on $E_j$ given as the intersection of the kernels of the maps `jointDelta (D j) i` — subject to `hactZ`: $(\mathrm{actZ}_j(\sigma) x)(\pi_E^j(\sigma) e) = \mathrm{sgn}(\sigma)\, x(e)$.
--
--   **The arrows (group `hg`, `hArr`, `hφ`, `hφC`, `hfinC`, `hsepC`, `hgalC_arr`, `hμV`, `hμE`, `hdeg`, `hμ_equiv`).** A type $\mathrm{Arr}$ with maps $\mathrm{dom}, \mathrm{cod} : \mathrm{Arr} \to J$ and $g : \mathrm{Arr} \to G$ such that each $\rho(g_\alpha)$ is type-preserving (`hg`) and $\Gamma_{\mathrm{dom}\,\alpha} \le$ the image of $\Gamma_{\mathrm{cod}\,\alpha}$ under conjugation by $g_\alpha$ (`hArr`). For each $\alpha$, a $C$-algebra map $\varphi_\alpha : FC_{\mathrm{cod}\,\alpha} \to FC_{\mathrm{dom}\,\alpha}$ which, read through the isomorphisms `eFC` inside $\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi\ \rho)$, is the action of $g_\alpha$ (`hφ`); $\varphi_\alpha$ is integral (`hφC`), makes $FC_{\mathrm{dom}\,\alpha}$ a finite module (`hfinC : FiniteAlong`) and a separable extension (`hsepC : SeparableAlong`) of $FC_{\mathrm{cod}\,\alpha}$, and commutes with the $S$-actions `galFC` (`hgalC_arr`). On the combinatorial side, a finite homomorphism $\mu_\alpha : (D_{\mathrm{dom}\,\alpha}).\mathrm{FiniteHom}\,(D_{\mathrm{cod}\,\alpha})$ — maps on vertices and edges commuting with $a$ and $b$, local degrees `deg`, `degV` and a total degree `degTotal` satisfying the multiplicativity of widths and the fibrewise degree sums — such that (`hμV`, `hμE`) `mapV` and `mapE` are induced by $v \mapsto \rho(g_\alpha)^{-1} \cdot v$ on vertex orbits and on dart orbits respectively, (`hdeg`) `degTotal` equals `finrankAlong C (φ α)`, and (`hμ_equiv`) `mapE` commutes with the permutation actions $\pi_E$ of $S$.
--
--   **Conclusion.** There is a family $\mathcal U$ assigning to each $j$ an object
--   $$\mathcal U_j : \mathtt{EquivariantUniformization}\ r\ (D_j)\ A\ hA\ \bigl(\mathrm{Pic}^0_C(FC_j)\bigr)\ S\ \mathrm{scalar}\ (\mathrm{actZ}_j)\ \bigl((\mathtt{DistribMulAction.toAddAut'}\ \ldots) \circ \mathrm{galFC}_j\bigr),$$
--   that is: an intermediate field $K \subseteq C$ over $\mathbb Q$; an additive map `ord` on $\mathrm{Additive}\,K^\times$ to $\mathbb Z$ with $v(k) = v(r)^{\mathrm{ord}(k)}$ for all units $k$; pointwise invariance of $K$ under every automorphism of $C$ over $\mathbb Q$ realising an element of the inertia subgroup; Hensel-type $n$-th roots in $K^\times$ for every $n > 0$ prime to $r$ of units of $\mathrm{ord}$ zero; a period datum $P$ for $D_j$ over $K \subseteq C$ with respect to `ord`; a surjective additive map `eFull` from `P.TorusPoints` (the $\mathbb Z$-linear maps from `ribbonKernel (D j)` to $\mathrm{Additive}\,C^\times$) onto $\mathrm{Pic}^0_C(FC_j)$, the group of degree-zero divisor classes of $FC_j$ over $C$, whose kernel is exactly the period lattice of $P$; and the $S$-equivariance of the period pairing $Q$ and of `eFull` with respect to `scalar`, $\mathrm{actZ}_j$ and the action of $S$ on $\mathrm{Pic}^0$ induced by $\mathrm{galFC}_j$ — together with the following four further properties.
--
--   (i) *Inertia invariants.* For every $j$ and every $z \in \mathrm{Pic}^0_C(FC_j)$ fixed by $\mathrm{galFC}_j(\iota\tau)$ for all $\tau$ in the decomposition group whose underlying automorphism lies in `A.inertiaSubgroupIn ℚ`, there exists a torus point $u$ of $\mathcal U_j$ with $(\mathcal U_j).\mathrm{eFull}\,u = z$ and such that $u$ is fixed by $(\mathcal U_j).P.\mathrm{coeffMap}\,s$ for every such inertial $\tau$ and every $s : C \simeq_{\mathbb Q} C$ inducing the action of $\tau$ on $C$.
--
--   (ii) *Compatibility with pull-back of divisors.* For every arrow $\alpha$, every torus point $u$ of $\mathcal U_{\mathrm{cod}\,\alpha}$ and degree-zero divisors $D_1$ on $FC_{\mathrm{cod}\,\alpha}$ and $D_1'$ on $FC_{\mathrm{dom}\,\alpha}$: if $(\mathcal U_{\mathrm{cod}\,\alpha}).\mathrm{eFull}\,u$ is the class of $D_1$ and $D_1'$ is `Divisor.pullbackAlong (φ α) (hφC α) D₁`, then $(\mathcal U_{\mathrm{dom}\,\alpha}).\mathrm{eFull}$ of $u$ composed with $(\mu_\alpha).\mathrm{pushforward}$ is the class of $D_1'$.
--
--   (iii) *Compatibility with push-forward of divisors.* Dually, for every arrow $\alpha$, every torus point $u'$ of $\mathcal U_{\mathrm{dom}\,\alpha}$ and degree-zero divisors $D_1'$ on $FC_{\mathrm{dom}\,\alpha}$ and $D_1$ on $FC_{\mathrm{cod}\,\alpha}$: if $(\mathcal U_{\mathrm{dom}\,\alpha}).\mathrm{eFull}\,u'$ is the class of $D_1'$ and $D_1$ is `Divisor.pushforwardAlong (φ α) (hφC α) D₁'`, then $(\mathcal U_{\mathrm{cod}\,\alpha}).\mathrm{eFull}$ of $u'$ composed with $(\mu_\alpha).\mathrm{pullback}$ is the class of $D_1$.
--
--   (iv) *Self-adjointness of the period pairings.* For every arrow $\alpha$, every $x \in \mathrm{ribbonKernel}(D_{\mathrm{cod}\,\alpha})$ and $y \in \mathrm{ribbonKernel}(D_{\mathrm{dom}\,\alpha})$, the period $Q$ of $\mathcal U_{\mathrm{dom}\,\alpha}$ at $((\mu_\alpha).\mathrm{pullback}\,x,\ y)$ and the period $Q$ of $\mathcal U_{\mathrm{cod}\,\alpha}$ at $(x,\ (\mu_\alpha).\mathrm{pushforward}\,y)$ have the same image in $C$.
--
--   This is the $p$-adic (Manin–Drinfeld, Mumford) uniformisation of the Jacobian of a Mumford quotient $\Gamma\backslash\Omega$, produced simultaneously for a whole family of such quotients and with the naturality required of it: the Galois and combinatorial actions match, inertia-invariant classes come from inertia-invariant torus points, and the degeneracy-graph push-forward and pull-back compute the conorm and norm maps on divisor classes along the finite morphisms of the family. It is used in the construction of Shimura curve models with good reduction carrying an equivariant uniformisation, in [`CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one

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

    (J : Type) (Γ : J → Subgroup G)
    (htp : ∀ j, (Γ j).map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [∀ j, Mumford.GraphAction ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ (j : J) (d : (BruhatTits.tree R₀ K₀).Dart), Finite (MulAction.stabilizer (↥((Γ j).map ρ)) d))

    (htame : ∀ (j : J) (w : LT.LatticeTree.Vertex R₀ K₀),
      Valued.v ((Nat.card ↥(MulAction.stabilizer ↥((Γ j).map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (FC : J → Type) [∀ j, Field (FC j)] [∀ j, Algebra A.valuation.Completion (FC j)] [hcurve : ∀ j, IsCurveOver A.valuation.Completion (FC j)]
    (eFC : ∀ j, FC j ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j)))
    (hfg : ∀ j, ∃ x : FC j, Transcendental A.valuation.Completion x ∧
      FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set (FC j))) (FC j))

    (E V : J → Type) [∀ j, Fintype (E j)] [∀ j, Fintype (V j)] [∀ j, DecidableEq (E j)] [∀ j, DecidableEq (V j)]
    (D : ∀ j, DegeneracyData (E j) (V j))
    (eV : ∀ j, Mumford.QuotVert ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V j)

    (eE : ∀ j, {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E j)
    (hDa : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), (D j).a (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), (D j).b (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), ((D j).w (eE j e) : ℕ) = Nat.card (MulAction.stabilizer (↥((Γ j).map ρ)) e.1.out))

    (galFC : ∀ j, S →* SemilinearAut A.valuation.Completion (FC j))
    (hgalFC_base : ∀ j (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC j σ) c = (scalar σ) • c)

    (hgal : ∀ j (σ : S), ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) ∧ (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))))

    (πV : ∀ j, S →* Equiv.Perm (V j)) (πE : ∀ j, S →* Equiv.Perm (E j)) (sgn : S →* ℤˣ)
    (hπV : ∀ j (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) →
      (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV j σ (eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ j (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) →
      (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ ((eE j).symm (πE j σ (eE j e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ ((eE j).symm (πE j σ (eE j e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ j σ e, (D j).w (πE j σ e) = (D j).w e)
    (hsgn_pos : ∀ j σ e, sgn σ = 1 → (D j).a (πE j σ e) = πV j σ ((D j).a e) ∧ (D j).b (πE j σ e) = πV j σ ((D j).b e))
    (hsgn_neg : ∀ j σ e, sgn σ = -1 → (D j).a (πE j σ e) = πV j σ ((D j).b e) ∧ (D j).b (πE j σ e) = πV j σ ((D j).a e))
    (hπ_inertia : ∀ j (τ : ↥(A.decompositionSubgroup ℚ)),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        πV j (ι τ) = 1 ∧ πE j (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : ∀ j, S →* (↥(ribbonKernel (D j)) ≃ₗ[ℤ] ↥(ribbonKernel (D j))))
    (hactZ : ∀ j (σ : S) (x : ↥(ribbonKernel (D j))) (e : E j),
      (actZ j σ x : E j → ℤ) (πE j σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E j → ℤ) e)

    (Arr : Type) (dom cod : Arr → J) (g : Arr → G) (hg : ∀ α, ρ (g α) ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hArr : ∀ α, Γ (dom α) ≤ (Γ (cod α)).map (MulAut.conj (g α)).toMonoidHom)

    (φ : ∀ α, (FC (cod α)) →ₐ[A.valuation.Completion] (FC (dom α)))
    (hφ : ∀ α (x : FC (cod α)),
      ((eFC (dom α) (φ α x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ (dom α)))) : FractionRing (Omega.HolRingOf ϖ ρ)) = (g α) • ((eFC (cod α) x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ (cod α)))) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : ∀ α, (φ α).toRingHom.IsIntegral)
    (hfinC : ∀ α, FiniteAlong A.valuation.Completion (φ α)) (hsepC : ∀ α, SeparableAlong A.valuation.Completion (φ α))
    (hgalC_arr : ∀ α (σ : S) (x : (FC (cod α))), galFC (dom α) σ • φ α x = φ α (galFC (cod α) σ • x))

    (μ : ∀ α, (D (dom α)).FiniteHom (D (cod α)))
    (hμV : ∀ α (v : LT.LatticeTree.Vertex R₀ K₀), (μ α).mapV (eV (dom α) (Quotient.mk (MulAction.orbitRel ↥((Γ (dom α)).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (cod α) (Quotient.mk (MulAction.orbitRel ↥((Γ (cod α)).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ (g α))⁻¹ • v)))
    (hμE : ∀ α (e : {e : Mumford.QuotEdge ↥((Γ (dom α)).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}),
      ((eE (cod α)).symm ((μ α).mapE (eE (dom α) e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ (cod α)).map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ (g α))⁻¹ • e.1.out)))
    (hdeg : ∀ α, ((μ α).degTotal : ℕ) = finrankAlong A.valuation.Completion (φ α))
    (hμ_equiv : ∀ α (σ : S) (e : E (dom α)), (μ α).mapE (πE (dom α) σ e) = πE (cod α) σ ((μ α).mapE e)) :
    ∃ 𝒰 : ∀ j, EquivariantUniformization r (D j) A hA (Pic0 A.valuation.Completion (FC j))
        S scalar (actZ j)
        ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion (FC j)) (Pic0 A.valuation.Completion (FC j))).comp (galFC j)),

      (∀ j (z : Pic0 A.valuation.Completion (FC j)),
        (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → galFC j (ι τ) • z = z) →
        ∃ u : (𝒰 j).P.TorusPoints,
          (∀ τ : ↥(A.decompositionSubgroup ℚ),
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
            ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) →
              (𝒰 j).P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
          (𝒰 j).eFull u = z) ∧

      (∀ α (u : (𝒰 (cod α)).P.TorusPoints)
          (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := (FC (cod α))))
          (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := (FC (dom α)))),
        (𝒰 (cod α)).eFull u = Pic0.mk D₁ →
        (D₁' : Divisor A.valuation.Completion (FC (dom α))) = Divisor.pullbackAlong (φ α) (hφC α) (D₁ : Divisor A.valuation.Completion (FC (cod α))) →
        (𝒰 (dom α)).eFull (u.comp (μ α).pushforward) = Pic0.mk D₁') ∧

      (∀ α (u' : (𝒰 (dom α)).P.TorusPoints)
          (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := (FC (dom α))))
          (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := (FC (cod α)))),
        (𝒰 (dom α)).eFull u' = Pic0.mk D₁' →
        (D₁ : Divisor A.valuation.Completion (FC (cod α))) = Divisor.pushforwardAlong (φ α) (hφC α) (D₁' : Divisor A.valuation.Completion (FC (dom α))) →
        (𝒰 (cod α)).eFull (u'.comp (μ α).pullback) = Pic0.mk D₁) ∧

      (∀ α (x : ↥(ribbonKernel (D (cod α)))) (y : ↥(ribbonKernel (D (dom α)))),
        ((((Additive.toMul ((𝒰 (dom α)).P.Q ((μ α).pullback x) y)) : (↥(𝒰 (dom α)).K)ˣ) : ↥(𝒰 (dom α)).K) : A.valuation.Completion) =
          ((((Additive.toMul ((𝒰 (cod α)).P.Q x ((μ α).pushforward y))) : (↥(𝒰 (cod α)).K)ˣ) : ↥(𝒰 (cod α)).K) : A.valuation.Completion)) := by sorry
