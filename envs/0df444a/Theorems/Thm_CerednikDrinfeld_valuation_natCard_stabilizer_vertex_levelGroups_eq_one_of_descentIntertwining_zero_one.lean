-- Prove2me | Theorems.Thm_CerednikDrinfeld_valuation_natCard_stabilizer_vertex_levelGroups_eq_one_of_descentIntertwining_zero_one
-- name    : CerednikDrinfeld.valuation_natCard_stabilizer_vertex_levelGroups_eq_one_of_descentIntertwining_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/756738d3-d488-5521-b220-3f8dcc1074fe
-- title:
--   Vertex stabilisers of the level groups have order prime to q
-- statement:
--   Throughout, $a_1,b_1\in\mathbb{Q}$ and $\mathbb{H}=\mathbb{H}[\mathbb{Q},a_1,b_1]$ is the associated quaternion algebra; $N$ is a nonzero natural number, assumed squarefree (`hN`), and $q,q'$ are primes with $5\le q$, $5\le q'$ (`hq5`, `hq'5`), $q'\neq q$ (`hqq'`), neither dividing $N$ (`hqN`, `hq'N`).
--
--   Quaternionic data. The hypothesis `hdef₁` is `IsDefiniteRamifiedExactlyAt a₁ b₁ q'`: $a_1<0$, $b_1<0$, and for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q'\in v$; so the distinguished finite ramification place is the one containing $q'$, not $q$. Further, $\Lambda_1,R_1$ are $\mathbb{Z}$-submodules of $\mathbb{H}$ with $\Lambda_1$ a maximal order (`hΛ₁`: an order which is maximal among orders containing it), $R_1$ an Eichler order of level $N$ (`hR₁`: $R_1=\Lambda'\sqcap\Lambda''$ for two maximal orders, with relative index $N$ in $\Lambda'$), and $R_1\le\Lambda_1$ (`hRΛ₁`). An idele $n_1\in(\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{f})^{\times}$ is given with `hn₁`: $n_1$ lies in the finite adelic box of $R_1$, $q\cdot n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $q^{-1}n_1$ do not. Writing $S_1=R_1\sqcap R_1^{n_1}$ for `meetOrder R₁ n₁`, the hypotheses are: `hS₁`, that $S_1$ is an Eichler order of level $Nq$; `hnorm₁`, that conjugation by $n_1$ fixes $S_1$; and `hsq₁`, that the shift by $n_1$ on the class set of the finite-idelic stabiliser of $S_1$ is an involution. Finally `hlaws₁` is `ClassSetHeckeLaws N q Λ₁ R₁ n₁`, whose four clauses state that the edge operators `classSetEdgeHecke N q Λ₁ R₁ n₁ ℓ` (given by the double-coset matrix of `uHeckeSet R₁ n₁ q` for $\ell=q$, of `levelHeckeUSet Λ₁ S₁ ℓ` for $\ell\mid N$, and of `primeHeckeSet S₁ ℓ` otherwise) commute pairwise; that the vertex operators `classSetVertexHecke N Λ₁ R₁ ℓ` (the matrix of `levelHeckeUSet Λ₁ R₁ ℓ` for $\ell\mid N$, of `primeHeckeSet R₁ ℓ` otherwise) commute pairwise; that for every prime $\ell\neq q$ and each of the two pushforwards `jointDelta (classSetDegeneracyData R₁ n₁) i` the edge operator is intertwined with the corresponding vertex operator; and that the edge operators preserve the common kernel of the two pushforwards.
--
--   The place above $q$. A valuation subring $A_2$ of $\overline{\mathbb{Q}}$ is given with `hA₂`: $q$ lies in the nonunits of $A_2$; $v_2$ is a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ containing $q$ (`hv₂`); and `hiso₂` records that the decomposition subgroup of $A_2$ over $\mathbb{Q}$ preserves $A_2$'s valuation. Put $K_0=$ [`ValuationSubring.ratClosure A₂`](def/ValuationSubring_CompletionRatClosure.html#L13), the closure of the prime subfield inside the completion $C=$ `A₂.valuation.Completion`. A splitting $\iota_2\colon\mathbb{H}\to M_2(K_0)$ is given, injective (`hι₂`), together with $\rho_2\colon\mathbb{H}^{\times}\to\mathrm{PGL}_2(K_0)$ and `hρ₂`, which says that $\rho_2$ is the projectivisation of the unit map of $\iota_2$. Next, $\varpi_2$ is a pseudo-uniformiser of $K_0$ relative to $C$ (an element of positive valuation less than $1$, with the scaling property) whose image in $C$ is $q$ (`hϖ₂`); `hdom₂` asserts that the ring `Omega.HolRingOf ϖ₂ ρ₂` of functions on the upper half-plane holomorphic on every affinoid of the $\varpi_2$-exhaustion is a domain. A homomorphism $\mathrm{dIso}_2$ from the decomposition subgroup to the isometric automorphisms of $C$ over $K_0$ is given, with `hdIso₂` identifying the underlying ring equivalence of $\mathrm{dIso}_2(\tau)$ with the action of $\tau$ on $C$.
--
--   Curves and the Hecke tower. $FN$ is a field over $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, every place has residue field finite over the base, and the module of Kähler differentials is free of rank one) and essentially of finite type; $\mathbb{T}$ is tower data `HeckeTower.TowerData q q' FN`, assigning to each prime $\ell\notin\{q,q'\}$ a curve field $\mathbb{T}.F\,\ell$ over $\overline{\mathbb{Q}}$ together with finite integral $\overline{\mathbb{Q}}$-algebra maps from $FN$ along the arrows. The hypothesis `hfg` requires, for each object $j$ of `HeckeTower.Obj q q'` (that is, `none` or `some ℓ`), a transcendental element $x$ of $\mathbb{T}$.`objField j` over which the field is finite-dimensional. Galois data consist of $\mathrm{gal}_N$ and, for each $\ell$, $\mathrm{gal}_T\,\ell$, homomorphisms from the decomposition subgroup of $A_2$ over $\mathbb{Q}$ to the semilinear automorphisms of $FN$, respectively $\mathbb{T}.F\,\ell$, over $\overline{\mathbb{Q}}$, whose base components are the given automorphisms of $\overline{\mathbb{Q}}$ (`hgalN`, `hgalT`); two semilinear automorphisms $W(i)$ of $FN$ and $W_T(\ell)(i)$ of $\mathbb{T}.F\,\ell$ are indexed by $i\in\mathrm{Fin}\,2$. A character $\chi_2$ from the decomposition subgroup to $\mathrm{Multiplicative}(\mathbb{Z}/2)$ and ring maps $\iota_{M,2}(j)\colon\mathbb{T}.\mathrm{objField}\,j\to\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$ are given. The hypothesis `hI` asserts the predicate [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) at $r=q$ and at the pair of indices $0,1$ in $\mathrm{Fin}\,2$, for the data $A_2,\rho_2,\varpi_2,\Gamma_2,w_2,\bar w_2,s_2,\mathrm{dIso}_2,FN,\mathbb{T},\mathrm{gal}_N,\mathrm{gal}_T,W,W_T,\chi_2,\iota_{M,2}$; among its clauses are that $\chi_2$ is trivial on inertia at $A_2$, is nontrivial at every Frobenius at $q$, and satisfies $\chi_2(\tau)=1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_2$ with $x^{q^2}=x$, and that each $\iota_{M,2}(j)$ restricts on $\overline{\mathbb{Q}}$ to the map into $C$ followed by the structure map; the remaining clauses, which tie $\iota_{M,2}$, the Galois actions, the involutions $W,W_T$, the level groups and the elements $w_2,\bar w_2,s_2$ together, are summarised here by name.
--
--   Group-theoretic data. Families $s_2(\ell)\in\mathbb{H}^{\times}$ and $sf_2(\ell)\in(\mathbb{H}\otimes\mathbb{A}^f)^{\times}$ are indexed by primes $\ell\notin\{q,q'\}$, subject to `hs₂`: for each $\ell$, the component of $sf_2(\ell)$ at a place $u$ not containing $q$ is $s_2(\ell)\otimes 1$; its component at a place containing $q$ is $1$; the product of the diagonal idele of the scalar $\ell$ with $sf_2(\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ S₁ ℓ` if $\ell\mid N$ and in `primeHeckeSet S₁ ℓ` otherwise; and $\mathrm{nrd}(s_2(\ell))=\ell$. The level groups $\Gamma_2(j)\le\mathbb{H}^{\times}$ satisfy `hΓ₂0`, which characterises $\Gamma_2(\mathrm{none})$ as the set of units lying in `CosetGraph.awayUnits R₁ v₂` (for every place $w\neq v_2$, the image under $\mathbb{H}^{\times}\to(\mathbb{H}\otimes\mathbb{Q}_w)^{\times}$ lies in the subgroup generated by the local box units of $R_1$ at $w$) and whose reduced norm has even $q$-adic valuation, and `hΓ₂ℓ`, which sets $\Gamma_2(\mathrm{some}\ \ell)=\Gamma_2(\mathrm{none})\sqcap s_2(\ell)\Gamma_2(\mathrm{none})s_2(\ell)^{-1}$. Interchange elements $w_2(j),\bar w_2(j)\in\mathbb{H}^{\times}$ are given with `hw₂`: $w_2(\mathrm{none})$ lies in `awayUnits R₁ v₂` and has reduced norm $q$, while $w_2(\mathrm{some}\ \ell)$ lies in `awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` and has reduced norm $q$; and `hwbar₂`, three clauses at the base object and the same three for each $\ell$: $\mathrm{nrd}(\bar w_2(j))=q'$; at every place $u\neq v_2$ not containing $q'$ the local image of $\bar w_2(j)$ is a local box unit of $R_1$ (respectively of `meetOrder R₁ (sf₂ ℓ)`); and at every place $u\neq v_2$ conjugation by $\bar w_2(j)$ preserves, in the sense of an equivalence, membership in the local box of $R_1$ (respectively of `meetOrder R₁ (sf₂ ℓ)`) and in the local box of $\Lambda_1$.
--
--   The valuation ring. Finally $R_0$ is a discrete valuation domain with finite residue field, an algebra over $K_0$ with $K_0$ as its fraction field, such that (`hR₀`) an element of $K_0$ lies in the image of $R_0$ exactly when its image in $C$ has valuation at most $1$.
--
--   Conclusion. For every object $j$ of `HeckeTower.Obj q q'` and every vertex $w$ of [`LT.LatticeTree.Vertex R₀ K₀`](def/LatticeTreeOrbital.html#L349), that is, every homothety class of full $R_0$-lattices, the valuation in $C$ of the natural number $\mathrm{Nat.card}$ of the stabiliser of $w$ in the image subgroup $\rho_2(\Gamma_2(j))\le\mathrm{PGL}_2(K_0)$, cast into $C$, equals $1$. Since `Nat.card` is $0$ for an infinite group and the valuation of $0$ is $0$, this single equality both asserts that each such vertex stabiliser is finite and that its order is a unit at the place, equivalently that $q$ does not divide it.
--
--   This is the statement, in the Čerednik–Drinfeld setting, that the groups acting on the Bruhat–Tits tree on the Mumford side of the uniformisation act with vertex stabilisers of order prime to $q$, the residue characteristic of the place $A_2$; the hypothesis that the primes involved are at least $5$ is what makes the finite subgroups of $\rho_2(\mathbb{H}^{\times})$ have order prime to $q$. It is used in the construction of a Shimura curve model with good reduction together with an equivariant uniformisation, where control of the stabilisers is needed to pass from the tree quotient to the formal scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_valuation_natCard_stabilizer_vertex_levelGroups_eq_one_of_descentIntertwining_zero_one.lean

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

set_option maxHeartbeats 400000 in

theorem CerednikDrinfeld.valuation_natCard_stabilizer_vertex_levelGroups_eq_one_of_descentIntertwining_zero_one

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₂ : Fact (A₂.DecompositionIsometric ℚ)]
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (hι₂ : Function.Injective ι₂)
    (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
    (hρ₂ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x))

    (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hϖ₂ : algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion))
    [hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂)]

    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)

    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))

    (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hdIso₂ : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x)

    (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂))
    (hI : CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
      FN 𝕋 galN galT W WT χ₂ ιM₂)

    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ValuationSubring.ratClosure A₂)] [IsFractionRing R₀ ↥(ValuationSubring.ratClosure A₂)] [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : ↥(ValuationSubring.ratClosure A₂), x ∈ Set.range (algebraMap R₀ ↥(ValuationSubring.ratClosure A₂)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion x) ≤ 1) :
    ∀ (j : HeckeTower.Obj q q') (w : LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)),
      Valued.v ((Nat.card ↥(MulAction.stabilizer ↥((Γ₂ j).map ρ₂) w) : ℕ) : A₂.valuation.Completion) = 1 := by sorry
