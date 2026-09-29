-- Prove2me | Theorems.Thm_CerednikDrinfeld_descentIntertwining_of_base_zero_one
-- name    : CerednikDrinfeld.descentIntertwining_of_base_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d61eac54-acf5-5854-8fff-20f892d749f8
-- title:
--   Čerednik–Drinfeld descent intertwining: all levels from the base level
-- statement:
--   Fix rationals $a_1,b_1$ and natural numbers $N,q,q'$ with $N\neq 0$, $N$ squarefree, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$, $5\le q$ and $5\le q'$.
--
--   **Quaternionic data at level $N$.** The hypothesis `hdef₁` is `IsDefiniteRamifiedExactlyAt a₁ b₁ q'`, i.e. $a_1<0$, $b_1<0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a_1,b_1]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $q'\in v$; note that the distinguished place is the one containing $q'$, not $q$. Two $\mathbb Z$-submodules $\Lambda_1,R_1$ of $\mathbb H[\mathbb Q,a_1,b_1]$ are given, with $\Lambda_1$ a maximal order (an order, in the sense of `IsOrder`: containing $1$, multiplicatively closed, $\mathbb Q$-spanning and finitely generated, and maximal among such under inclusion), $R_1$ an Eichler order of level $N$ (an intersection of two maximal orders whose relative additive index in the first is $N$), and $R_1\le\Lambda_1$.
--
--   An adelic unit $n_1\in(\mathbb H[\mathbb Q,a_1,b_1]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}})^\times$ is assumed to lie in `primeHeckeSet R₁ q`: $n_1$ lies in the adelic box of $R_1$, $q\,n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $q^{-1}n_1$ do not. Writing `meetOrder R₁ n₁` $=R_1\cap n_1R_1n_1^{-1}$ (conjugation being [`Submodule.conjByFiniteIdele`](def/Submodule_FiniteAdeleBox.html#L31)), the hypotheses require: `hS₁`, that this intersection is an Eichler order of level $Nq$; `hnorm₁`, that it is stable under conjugation by $n_1$; and `hsq₁`, that the shift by $n_1$ on the class set of the stabiliser of its adelic box (the double coset space of [`Submodule.finiteIdeleDiagonal`](def/Submodule_FiniteAdeleBox.html#L43)-rational points against that stabiliser) is an involution. The class sets attached to `meetOrder R₁ n₁` and to $R_1$ are assumed finite.
--
--   The hypothesis `hlaws₁` is `ClassSetHeckeLaws N q Λ₁ R₁ n₁`, four clauses on the integral matrices `classSetEdgeHecke N q Λ₁ R₁ n₁ ℓ` (the Hecke matrix of `uHeckeSet R₁ n₁ q` when $\ell=q$, of `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` when $\ell\mid N$, and of `primeHeckeSet (meetOrder R₁ n₁) ℓ` otherwise) and `classSetVertexHecke N Λ₁ R₁ ℓ` (of `levelHeckeUSet Λ₁ R₁ ℓ` when $\ell\mid N$, of `primeHeckeSet R₁ ℓ` otherwise): the edge matrices commute pairwise, the vertex matrices commute pairwise, for every prime $\ell\neq q$ and each $i\in\{0,1\}$ the $i$-th degeneracy pushforward of `classSetDegeneracyData R₁ n₁` intertwines the edge and vertex operators at $\ell$, and for every prime $\ell$ the edge operator preserves the common kernel of the two degeneracy pushforwards.
--
--   **The place over $q$ and the $q$-adic period data.** A valuation subring $A_2$ of $\overline{\mathbb Q}$ is given with $(q:\overline{\mathbb Q})$ a nonunit of $A_2$, together with the hypothesis that every element of its decomposition subgroup over $\mathbb Q$ preserves the valuation, and a height-one prime $v_2$ of $\mathcal O_{\mathbb Q}$ with $q\in v_2$. An injective $\mathbb Q$-algebra map $\iota_2$ of $\mathbb H[\mathbb Q,a_1,b_1]$ into $2\times 2$ matrices over [`ValuationSubring.ratClosure A₂`](def/ValuationSubring_CompletionRatClosure.html#L13) (the closure of the prime subfield inside the completion $A_2.\mathrm{valuation.Completion}$) is given, and a homomorphism $\rho_2$ from the unit group of the quaternion algebra to $\mathrm{PGL}_2$ of that subfield, required by `hρ₂` to be the projectivisation of $\iota_2$. A pseudo-uniformizer $\varpi_2$ (an element of the subfield whose valuation in the completion lies strictly between $0$ and $1$ and which scales every nonzero element in the sense of `PseudoUniformizer.scale`) is given, with `hϖ₂` identifying its image in the completion with the image of $q$; the ring `Omega.HolRingOf ϖ₂ ρ₂` of functions holomorphic on all the affinoids is assumed to be a domain. A homomorphism $\mathrm{dIso}_2$ from the decomposition subgroup to the isometric automorphisms of the completion over that subfield is given, realising by `hdIso₂` the natural Galois action $x\mapsto\tau\cdot x$.
--
--   **Hecke tower of function fields.** A field $F_N$ is given which is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors, finite residue fields at all places, and $\Omega^1$ free of rank one) and essentially of finite type over $\overline{\mathbb Q}$, together with $\mathbb T$ : `HeckeTower.TowerData q q' FN`, i.e. fields $\mathbb T.F_\ell$ indexed by the primes $\ell\nmid qq'$, each a curve over $\overline{\mathbb Q}$ essentially of finite type, and for each arrow $\alpha=(\ell,i)$ with $i\in\{0,1\}$ a $\overline{\mathbb Q}$-algebra map $\mathbb T.\varphi_\alpha\colon F_N\to\mathbb T.F_\ell$ which is finite and integral. The hypothesis `hfg` asks that each field $\mathbb T.\mathrm{objField}\,j$ ($j$ either the base object or some $\ell$) contain an element $x$ transcendental over $\overline{\mathbb Q}$ with $\mathbb T.\mathrm{objField}\,j$ finite over $\overline{\mathbb Q}(x)$. Semilinear automorphism data are given: $\mathrm{gal}_N$ and, for each $\ell$, $\mathrm{gal}_T\,\ell$, homomorphisms from the decomposition subgroup of $A_2$ over $\mathbb Q$ into the semilinear automorphisms of $F_N$, respectively of $\mathbb T.F_\ell$, whose base automorphism is $\tau$ itself (hypotheses `hgalN`, `hgalT`), and involution candidates $W\colon\{0,1\}\to\mathrm{SemilinearAut}(\overline{\mathbb Q},F_N)$ and $W_T\,\ell$ at each $\ell$. The compatibilities along the degeneracy maps are `hgalφ`, that $\mathrm{gal}_T\,\alpha_1\tau$ followed by nothing commutes with $\mathbb T.\varphi_\alpha$, i.e. $\mathrm{gal}_T\,\alpha_1\tau\cdot\mathbb T.\varphi_\alpha(x)=\mathbb T.\varphi_\alpha(\mathrm{gal}_N\tau\cdot x)$ for all $\tau$ and $x\in F_N$; `hWφ`, the same identity with $W_T\,\alpha_1\,i$ and $W\,i$; and `hdeg`, that `finrankAlong` of $\mathbb T.\varphi_\alpha$ equals `HeckeTower.arrowDegree N α`, namely $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise.
--
--   **Uniformising groups and Atkin–Lehner elements.** For each prime $\ell\nmid qq'$ a global unit $s_2\ell$ and an adelic unit $\mathrm{sf}_2\ell$ are given, subject to `hs₂`: the component of $\mathrm{sf}_2\ell$ at each place $u$ not containing $q$ is $s_2\ell\otimes 1$; its component at each place containing $q$ is $1$; the product of the diagonal adelic image of the rational scalar $\ell$ with $(\mathrm{sf}_2\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₁ n₁) ℓ` otherwise; and $\mathrm{nrd}(s_2\ell)=\ell$. Subgroups $\Gamma_2 j$ of the quaternionic unit group are given with `hΓ₂0`: $x\in\Gamma_2(\mathrm{none})$ iff $x$ lies in `CosetGraph.awayUnits R₁ v₂` (its image in each localisation at $w\neq v_2$ lies in the subgroup generated by the units of the local box of $R_1$ at $w$) and $\mathrm{ord}_q(\mathrm{nrd}\,x)$ is even; and `hΓ₂ℓ`: $\Gamma_2(\mathrm{some}\,\ell)=\Gamma_2(\mathrm{none})\cap s_2\ell\,\Gamma_2(\mathrm{none})\,(s_2\ell)^{-1}$.
--
--   Two further families $w_2,\bar w_2$ of quaternionic units indexed by the objects are given. The hypothesis `hw₂` requires $w_2(\mathrm{none})\in$ `awayUnits R₁ v₂` with $\mathrm{nrd}=q$, and for each $\ell$, $w_2(\mathrm{some}\,\ell)\in$ `awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` with $\mathrm{nrd}=q$. The hypothesis `hwbar₂` requires, at the base object, that $\mathrm{nrd}(\bar w_2(\mathrm{none}))=q'$, that at every place $u\neq v_2$ not containing $q'$ the local image of $\bar w_2(\mathrm{none})$ is a unit of the local box of $R_1$ at $u$, and that at every place $u\neq v_2$ conjugation $x\mapsto \bar w_2(\mathrm{none})^{-1}x\,\bar w_2(\mathrm{none})$ preserves the local box of $R_1$ at $u$ and the local box of $\Lambda_1$ at $u$, in each case as an equivalence; and for each $\ell$ the same three conditions for $\bar w_2(\mathrm{some}\,\ell)$, with `meetOrder R₁ (sf₂ ℓ)` in place of $R_1$ and with $\Lambda_1$ unchanged.
--
--   Finally a character $\chi_2$ from the decomposition subgroup to $\mathrm{Multiplicative}(\mathbb Z/2)$ is given, and for each object $j$ a ring homomorphism $\iota_{M,2}\,j\colon\mathbb T.\mathrm{objField}\,j\to\mathrm{Frac}\,(\mathrm{HolRingOf}\ \varpi_2\ \rho_2)$.
--
--   **Hypothesis on the base level and conclusion.** Assuming `hBase`, that [`CerednikDrinfeld.DescentIntertwiningBase`](def/CerednikDrinfeld_DescentIntertwiningBase.html#L17) holds for the data $q$, the indices $0$ and $1$ of $\mathrm{Fin}\,2$, $A_2$, $\rho_2$, $\varpi_2$, $\Gamma_2$, $w_2$, $\bar w_2$, $s_2$, $\mathrm{dIso}_2$, $F_N$, $\mathbb T$, $\mathrm{gal}_N$, $\mathrm{gal}_T$, $W$, $W_T$, $\chi_2$, $\iota_{M,2}$, the conclusion is that [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) holds for exactly the same tuple, with $r=q$ and the same two distinguished indices $0$ and $1$. Its clauses are: $\chi_2\tau=1$ for every $\tau$ whose underlying $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lies in the inertia subgroup of $A_2$; $\chi_2\varphi\neq 1$ for every $\varphi$ that is a Frobenius at $q$ for $A_2$, in the sense that it acts on the residue field of $A_2$ by $x\mapsto x^{q}$; the equivalence, for every $\tau$, of $\chi_2\tau=1$ with $\tau$ fixing every element $x$ of the residue field of $A_2$ satisfying $x^{q^2}=x$; for every object $j$ of the tower and every $z\in\overline{\mathbb Q}$, the identity $\iota_{M,2}\,j(\text{image of }z\text{ in }\mathbb T.\mathrm{objField}\,j)=$ the image of $z$ in $\mathrm{Frac}\,(\mathrm{HolRingOf}\ \varpi_2\ \rho_2)$ under the structural map from the completion; and the remaining clauses of `DescentIntertwining`, quantified over the objects $j$, which impose at each object the level-$j$ form of the conditions that `DescentIntertwiningBase` imposes at the base object, the groups $\Gamma_2 j$, the elements $w_2 j$, $\bar w_2 j$, $s_2\ell$, the semilinear data and the character $\chi_2$ entering as indicated. The content of the theorem is thus the passage from the base-level predicate to the all-levels predicate on one and the same argument tuple.
--
--   This is the inductive step of Čerednik's interchange for the prime-to-$qq'$ Hecke tower: the $q$-adic uniformisation data for a Shimura curve of level $N$, once known at the base level together with the degeneracy and tower compatibilities, propagates to every level $N\ell$. It feeds the existence statement that produces simultaneously a Shimura-curve model, a Hecke tower of function fields and the Čerednik interchange pair over all levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_descentIntertwining_of_base_zero_one.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford
open scoped Classical

theorem CerednikDrinfeld.descentIntertwining_of_base_zero_one

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

    (hgalφ : ∀ (α : HeckeTower.Arr q q') (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : FN), galT α.1 τ • 𝕋.φ α x = 𝕋.φ α (galN τ • x))
    (hWφ : ∀ (α : HeckeTower.Arr q q') (i : Fin 2) (x : FN), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x))
    (hdeg : ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α)
    (hBase : CerednikDrinfeld.DescentIntertwiningBase q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
      FN 𝕋 galN galT W WT χ₂ ιM₂) :
    CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
      FN 𝕋 galN galT W WT χ₂ ιM₂ := by sorry
