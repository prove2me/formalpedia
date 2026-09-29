-- Prove2me | Theorems.Thm_CerednikDrinfeld_HeckeTower_smul_phi_eq_phi_smul_of_descentIntertwining_one_zero
-- name    : CerednikDrinfeld.HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/3f13d74d-cf49-52af-8ecb-f0a96141d746
-- title:
--   Degeneracy maps intertwine Galois and Atkin–Lehner actions
-- statement:
--   Fix rationals $a_2,b_2$ and the quaternion algebra $\mathbb{H}[\mathbb{Q},a_2,b_2]$, natural numbers $N,q,q'$ with $N$ nonzero and squarefree, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$, $5\le q$ and $5\le q'$.
--
--   *Quaternionic data.* The hypothesis `hdef₂` says that $a_2<0$, $b_2<0$ and that, for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a_2,b_2]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q\in v$. Two $\mathbb{Z}$-submodules $\Lambda_2,R_2$ of $\mathbb{H}[\mathbb{Q},a_2,b_2]$ are given with $R_2\le\Lambda_2$, where $\Lambda_2$ is a maximal order (an order, i.e. containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning and finitely generated, and maximal among the orders containing it) and $R_2$ is an Eichler order of level $N$, that is, an intersection $\Lambda_1\sqcap\Lambda_2'$ of two maximal orders whose relative index in $\Lambda_1$ is $N$. A unit $n_2$ of $\mathbb{H}[\mathbb{Q},a_2,b_2]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{f}}$ is given lying in `primeHeckeSet R₂ q'`: $n_2$ lies in the finite adelic box of $R_2$, so does $q'\,n_2^{-1}$, while $n_2^{-1}$ and $q'^{-1}n_2$ do not. The order $\mathrm{meetOrder}\,R_2\,n_2=R_2\sqcap n_2R_2n_2^{-1}$ is assumed to be an Eichler order of level $Nq'$ (`hS₂`) and to be stable under conjugation by $n_2$ (`hnorm₂`); on the class set of the finite-idele stabiliser of $\mathrm{meetOrder}\,R_2\,n_2$ — the double coset quotient of the idele units by the diagonal image of $\mathbb{H}[\mathbb{Q},a_2,b_2]^{\times}$ and by the stabiliser of the adelic box — right translation by $n_2$ is an involution (`hsq₂`), the relevant class sets being finite. The hypothesis `hlaws₂` is `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`: the edge Hecke matrices at all primes commute with one another, the vertex Hecke matrices at all primes commute with one another, for every prime $\ell\neq q'$ and every $i\in\{0,1\}$ the $i$-th degeneracy pushforward `jointDelta` of `classSetDegeneracyData R₂ n₂` carries the edge Hecke operator at $\ell$ to the vertex Hecke operator at $\ell$, and the joint kernel of the two degeneracy pushforwards is stable under every edge Hecke operator.
--
--   *The place and the $p$-adic uniformising data.* A valuation subring $A_1$ of $\overline{\mathbb{Q}}$ is given with $q'$ in its nonunits (`hA₁`), all elements of its decomposition subgroup over $\mathbb{Q}$ being isometries for its valuation (`hiso₁`), together with a height-one prime $v_1$ of $\mathcal{O}_{\mathbb{Q}}$ containing $q'$. An injective $\mathbb{Q}$-algebra map $\iota_1$ from $\mathbb{H}[\mathbb{Q},a_2,b_2]$ into $2\times 2$ matrices over $\mathrm{ratClosure}\,A_1$ (the topological closure of the prime subfield inside the completion of $A_1$'s valuation) is given, and $\rho_1:\mathbb{H}[\mathbb{Q},a_2,b_2]^{\times}\to \mathrm{PGL}_2(\mathrm{ratClosure}\,A_1)$ is the induced projective representation (`hρ₁`). A pseudo-uniformiser $\varpi_1$ for $\mathrm{ratClosure}\,A_1$ in the completion — an element of valuation strictly between $0$ and $1$ satisfying the scaling condition — is given whose image in the completion is $q'$ (`hϖ₁`), and the ring `HolRingOf ϖ₁ ρ₁` of functions on the upper half plane holomorphic on every affinoid is assumed to be a domain. A homomorphism $\mathrm{dIso}_1$ from the decomposition subgroup to the valuation-preserving ring automorphisms of the completion fixing $\mathrm{ratClosure}\,A_1$ is given, realising the Galois action (`hdIso₁`), and $\chi_1$ is a homomorphism from the decomposition subgroup to $\mathbb{Z}/2$ written multiplicatively.
--
--   *The tower.* $F_N$ is a field, an algebra over $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` (principal divisors exist, each place has residue field finite over $\overline{\mathbb{Q}}$, and the module of Kähler differentials is free of rank one) and is essentially of finite type. $\mathbb{T}$ is a `HeckeTower.TowerData q q' FN`: for each prime $\ell$ with $\ell\neq q,q'$ a field $\mathbb{T}.F\,\ell$ which is likewise a curve over $\overline{\mathbb{Q}}$ and essentially of finite type, together with, for each arrow $\alpha$, a $\overline{\mathbb{Q}}$-algebra map $\mathbb{T}.\varphi\,\alpha$ from $F_N$ to $\mathbb{T}.F\,\alpha_1$ which is finite and integral. The hypothesis `hfg` requires each field $\mathbb{T}.\mathrm{objField}\,j$ ($F_N$ for $j=\mathrm{none}$, $\mathbb{T}.F\,\ell$ for $j=\mathrm{some}\,\ell$) to contain an element transcendental over $\overline{\mathbb{Q}}$ over whose generated subfield it is finite-dimensional. Semilinear actions are given: $\mathrm{galN}$ from the decomposition subgroup of $A_1$ to the group of pairs (ring automorphism of $F_N$, ring automorphism of $\overline{\mathbb{Q}}$) compatible with the structure map, and $\mathrm{galT}\,\ell$ likewise on $\mathbb{T}.F\,\ell$, with base components equal to the given element of the decomposition subgroup (`hgalN`, `hgalT`). Further, $W:\{0,1\}\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},F_N)$ and $WT\,\ell:\{0,1\}\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},\mathbb{T}.F\,\ell)$ are the Atkin–Lehner candidates, and $\iota M_1$ assigns to each object $j$ a ring homomorphism from $\mathbb{T}.\mathrm{objField}\,j$ into the fraction field of `HolRingOf ϖ₁ ρ₁`.
--
--   *Arithmetic groups and involution elements.* Elements $s_1(\ell)\in\mathbb{H}[\mathbb{Q},a_2,b_2]^{\times}$ and ideles $sf_1(\ell)$ are given, with, for each $\ell$ (`hs₁`): the component of $sf_1(\ell)$ at a prime $u$ not containing $q'$ is $s_1(\ell)\otimes 1$; its component at a prime containing $q'$ is $1$; the product of the diagonal idele of the scalar $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise; and $\mathrm{nrd}(s_1(\ell))=\ell$, where $\mathrm{nrd}$ is the reduced norm $x_0^2-a_2x_1^2-b_2x_2^2+a_2b_2x_3^2$. The groups $\Gamma_1$ are prescribed by: $\Gamma_1(\mathrm{none})$ consists of the units lying in `awayUnits R₂ v₁` — those whose local image at every prime $w\neq v_1$ lies in the subgroup generated by the local box units of $R_2$ at $w$ — and having even $q'$-adic valuation of reduced norm (`hΓ₁0`), and $\Gamma_1(\mathrm{some}\,\ell)=\Gamma_1(\mathrm{none})\sqcap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$ (`hΓ₁ℓ`). Elements $w_1,\bar{w}_1$ indexed by the objects are given with: $w_1(\mathrm{none})\in\mathrm{awayUnits}\,R_2\,v_1$ and $\mathrm{nrd}\,w_1(\mathrm{none})=q'$, and for each $\ell$, $w_1(\mathrm{some}\,\ell)\in\mathrm{awayUnits}(\mathrm{meetOrder}\,R_2\,(sf_1\ell))\,v_1$ with reduced norm $q'$ (`hw₁`); and (`hwbar₁`) $\mathrm{nrd}\,\bar{w}_1(\mathrm{none})=q$, the local image of $\bar{w}_1(\mathrm{none})$ at each prime $u\neq v_1$ not containing $q$ is a local box unit of $R_2$, and conjugation by $\bar{w}_1(\mathrm{none})$ preserves membership in the local boxes of $R_2$ and of $\Lambda_2$ at every prime $u\neq v_1$; the same three conditions are imposed on $\bar{w}_1(\mathrm{some}\,\ell)$ with $\mathrm{meetOrder}\,R_2\,(sf_1\ell)$ in place of $R_2$.
--
--   *The interchange hypothesis.* Finally `hI` asserts `DescentIntertwining q' 1 0 A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁ FN 𝕋 galN galT W WT χ₁ ιM₁`, with $r=q'$ and with the two indices $1$ and $0$ selecting the Atkin–Lehner candidates attached to $w_1$ and to $\bar{w}_1$. Its first clauses require $\chi_1$ to be trivial on the inertia subgroup, to be nontrivial on any Frobenius element at $q'$, and to satisfy $\chi_1(\tau)=1$ exactly when $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2}=x$; a further clause requires each $\iota M_1(j)$ to send a scalar from $\overline{\mathbb{Q}}$ to its image in the completion. The remaining clauses of the predicate couple the embeddings $\iota M_1$ with the groups $\Gamma_1$, the elements $w_1,\bar{w}_1,s_1$, the isometries $\mathrm{dIso}_1$, the character $\chi_1$ and the semilinear data $\mathrm{galN},\mathrm{galT},W,WT$.
--
--   *Conclusion.* Two assertions hold. First, for every prime $\ell$ with $\ell\neq q,q'$, every $i\in\{0,1\}$, every $\tau$ in the decomposition subgroup of $A_1$ over $\mathbb{Q}$ and every $x\in F_N$,
--   $$\mathrm{galT}\,\ell\,(\tau)\cdot \mathbb{T}.\varphi\,(\ell,i)(x)=\mathbb{T}.\varphi\,(\ell,i)\bigl(\mathrm{galN}(\tau)\cdot x\bigr).$$
--   Second, for every such $\ell$, all $i,k\in\{0,1\}$ and every $x\in F_N$,
--   $$WT\,\ell\,(k)\cdot \mathbb{T}.\varphi\,(\ell,i)(x)=\mathbb{T}.\varphi\,(\ell,i)\bigl(W(k)\cdot x\bigr).$$
--
--   This is the arrow-equivariance statement for a prime-to-$qq'$ Hecke tower of curves over $\overline{\mathbb{Q}}$ equipped with Čerednik-type interchange data at a place above $q'$: the degeneracy maps of the tower commute with the semilinear Galois actions and with the two Atkin–Lehner candidates on base and level fields. It feeds the construction of the symmetry group and of the invariant subfield in [`CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero`](thm.html#CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero), and relies on the Atkin–Lehner relations for the level groups at a place, [`CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place`](thm.html#CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_HeckeTower_smul_phi_eq_phi_smul_of_descentIntertwining_one_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.HeckeTower.smul_phi_eq_phi_smul_of_descentIntertwining_one_zero

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁))
    (hI : CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁)
    :
    (∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : FN),
        galT ℓ τ • 𝕋.φ (ℓ, i) x = 𝕋.φ (ℓ, i) (galN τ • x)) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (i k : Fin 2) (x : FN),
        WT ℓ k • 𝕋.φ (ℓ, i) x = 𝕋.φ (ℓ, i) (W k • x)) := by sorry
