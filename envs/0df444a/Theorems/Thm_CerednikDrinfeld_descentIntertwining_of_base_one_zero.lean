-- Prove2me | Theorems.Thm_CerednikDrinfeld_descentIntertwining_of_base_one_zero
-- name    : CerednikDrinfeld.descentIntertwining_of_base_one_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/3722a444-8907-52a4-b1ac-91a2c9228b0f
-- title:
--   Čerednik descent intertwining: base level implies all levels
-- statement:
--   The data are organised in several blocks.
--
--   *Quaternionic data.* Rationals $a_2,b_2$, a natural number $N$ with `NeZero N` and squarefree (`hN`), and primes $q,q'$ with $q\nmid N$ (`hqN`), $q'\nmid N$ (`hq'N`), $q'\neq q$ (`hqq'`) and $q,q'\ge 5$ (`hq5`, `hq'5`). The hypothesis `hdef₂` (`IsDefiniteRamifiedExactlyAt a₂ b₂ q`) says $a_2<0$, $b_2<0$ and that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $q\in v$. Two $\mathbb Z$-submodules $\Lambda_2,R_2$ of $\mathbb H[\mathbb Q,a_2,b_2]$ are given with $\Lambda_2$ a maximal order (`hΛ₂`: an order maximal among the orders containing it), $R_2$ an Eichler order of level $N$ (`hR₂`: an intersection of two maximal orders whose relative index in the first is $N$), and $R_2\le\Lambda_2$ (`hRΛ₂`).
--
--   *Hecke element at $q'$ and class-set laws.* A unit $n_2$ of $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ with $n_2\in$ `primeHeckeSet R₂ q'` (`hn₂`: $n_2$ lies in the adelic box of $R_2$, $q'\,n_2^{-1}$ lies in that box, while $n_2^{-1}$ and $q'^{-1}n_2$ do not). Writing $S_2=$ `meetOrder R₂ n₂` $=R_2\cap n_2R_2n_2^{-1}$, the hypotheses are: `hS₂`, that $S_2$ is an Eichler order of level $Nq'$; `hnorm₂`, that conjugation by $n_2$ fixes $S_2$; `hsq₂`, that the shift by $n_2$ on the class set $\mathrm{ClassSet}$ of the finite-idele stabiliser of $S_2$ (double cosets of the diagonal image of $\mathbb H[\mathbb Q,a_2,b_2]^{\times}$ and of that stabiliser, with a representative multiplied on the right by $n_2$) is an involution; finiteness and decidability of the two class sets; and `hlaws₂` (`ClassSetHeckeLaws N q' Λ₂ R₂ n₂`), namely that the edge Hecke matrices on $\mathrm{ClassSet}$ of $S_2$ pairwise commute, that the vertex Hecke matrices on $\mathrm{ClassSet}$ of $R_2$ pairwise commute, that for every prime $\ell\ne q'$ and each $i\in\{0,1\}$ the map $\mathrm{jointDelta}$ of the degeneracy datum of $(R_2,n_2)$ carries the edge Hecke action to the vertex Hecke action, and that the joint kernel of the two $\mathrm{jointDelta}$ maps is stable under every edge Hecke operator.
--
--   *The place over $q'$ and the $q'$-adic frame.* A valuation subring $A_1$ of $\overline{\mathbb Q}$ with $q'$ a nonunit of $A_1$ (`hA₁`), decomposition-isometric over $\mathbb Q$ (`hiso₁`: the decomposition subgroup preserves the valuation), a height-one prime $v_1$ of $\mathcal O_{\mathbb Q}$ containing $q'$ (`hv₁`), an injective $\mathbb Q$-algebra embedding $\iota_1$ of $\mathbb H[\mathbb Q,a_2,b_2]$ into $2\times 2$ matrices over the closure [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13) of the prime subfield inside the completion $C$ of $A_1$'s valuation (`hι₁`), a homomorphism $\rho_1$ to $\mathrm{PGL}(2,\cdot)$ over that closure which on units is the projectivisation of $\iota_1$ (`hρ₁`), a pseudo-uniformiser $\varpi_1$ whose image in $C$ is $q'$ (`hϖ₁`), with `HolRingOf ϖ₁ ρ₁` a domain (`hdom₁`), and a homomorphism $d_1$ from the decomposition subgroup to the isometric automorphisms of $C$ inducing the natural action (`hdIso₁`).
--
--   *The abstract Hecke tower.* A field $F_N$ over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ (finite residue fields at all places, principal divisors, free rank-one Kähler module) and of essentially finite type, together with tower data $\mathbb T$ of type `HeckeTower.TowerData q q' FN`: fields $\mathbb T.F\,\ell$ for each prime $\ell\notin\{q,q'\}$, and for each arrow $\alpha=(\ell,i)$ with $i\in\{0,1\}$ a $\overline{\mathbb Q}$-algebra map $\mathbb T.\varphi\,\alpha:F_N\to\mathbb T.F\,\ell$ which is finite and integral. `hfg` requires every field of the tower (the base $F_N$ and each $\mathbb T.F\,\ell$) to contain an element transcendental over $\overline{\mathbb Q}$ over which the field is finite. Semilinear automorphism actions $\mathrm{gal}_N$ on $F_N$ and $\mathrm{gal}_T\,\ell$ on $\mathbb T.F\,\ell$ of the decomposition subgroup of $A_1$ are given, with base parts the given automorphisms of $\overline{\mathbb Q}$ (`hgalN`, `hgalT`), and semilinear automorphisms $W_0,W_1$ of $F_N$ and $WT\,\ell$ of each $\mathbb T.F\,\ell$. The compatibilities are: `hgalφ`, that each $\mathbb T.\varphi\,\alpha$ intertwines $\mathrm{gal}_N$ with $\mathrm{gal}_T\,\alpha.1$; `hWφ`, that it intertwines $W_i$ with $WT\,\alpha.1\,i$ for each $i$; and `hdeg`, that the degree of $\mathbb T.F\,\alpha.1$ over the image of $\mathbb T.\varphi\,\alpha$ equals `HeckeTower.arrowDegree N α`, which is $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise.
--
--   *Discrete groups and Atkin–Lehner elements.* Quaternion units $s_1\ell$ and adelic units $sf_1\ell$ for each prime $\ell\notin\{q,q'\}$ satisfying `hs₁`: the localisation of $sf_1\ell$ at each $u$ not containing $q'$ is $s_1\ell\otimes 1$, its localisation at each $u$ containing $q'$ is $1$, the product of the diagonal adelic image of the scalar $\ell$ with $(sf_1\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ S₂ ℓ` when $\ell\mid N$ (that is, in `primeHeckeSet S₂ ℓ` with conjugation of $S_2$ moving $S_2$ and with $S_2$ not contained in the conjugate of $\Lambda_2$) and in `primeHeckeSet S₂ ℓ` otherwise, and $\mathrm{nrd}(s_1\ell)=\ell$. A family of subgroups $\Gamma_1$ indexed by the objects of the tower with: `hΓ₁0`, $\Gamma_1(\mathrm{none})$ consists of the units lying in `awayUnits R₂ v₁` (for every place $w\ne v_1$, the image in the $w$-localisation lies in the subgroup generated by the local box units of $R_2$ at $w$) whose reduced norm has even $q'$-adic valuation; and `hΓ₁ℓ`, $\Gamma_1(\mathrm{some}\ \ell)=\Gamma_1(\mathrm{none})\cap s_1\ell\,\Gamma_1(\mathrm{none})\,(s_1\ell)^{-1}$. Elements $w_1,\bar w_1$ indexed by the objects: `hw₁` requires $w_1(\mathrm{none})\in$ `awayUnits R₂ v₁` with reduced norm $q'$, and $w_1(\mathrm{some}\ \ell)\in$ `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; `hwbar₁` requires, at the base object, $\mathrm{nrd}(\bar w_1(\mathrm{none}))=q$, that for every $u\ne v_1$ not containing $q$ the localisation of $\bar w_1(\mathrm{none})$ lies in the local box units of $R_2$ at $u$, and that for every $u\ne v_1$ conjugation by $\bar w_1(\mathrm{none})$ preserves the local box of $R_2$ at $u$ and the local box of $\Lambda_2$ at $u$ (both as two-sided membership equivalences), and the same three conditions at each object $\mathrm{some}\ \ell$ with $R_2$ replaced by `meetOrder R₂ (sf₁ ℓ)`.
--
--   *The intertwining data.* A homomorphism $\chi_1$ from the decomposition subgroup of $A_1$ to $\mathrm{Multiplicative}(\mathbb Z/2)$, and for each object $j$ of the tower a ring homomorphism $\iota M_1\,j$ from $\mathbb T.\mathrm{objField}\,j$ to the fraction field of `HolRingOf ϖ₁ ρ₁`.
--
--   *Hypothesis.* `hBase`: the predicate `DescentIntertwiningBase` holds for the parameters $r=q'$, $ir=1$, $irbar=0$ and the tuple $(A_1,\rho_1,\varpi_1,\Gamma_1,w_1,\bar w_1,s_1,d_1,F_N,\mathbb T,\mathrm{gal}_N,\mathrm{gal}_T,W,WT,\chi_1,\iota M_1)$. Its clauses comprise: $\chi_1$ is trivial on the elements of the decomposition subgroup lying in the inertia subgroup of $A_1$ over $\mathbb Q$; $\chi_1$ is nontrivial on every element which is a Frobenius at $q'$ for $A_1$; $\chi_1(\tau)=1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2}=x$; the normalisation $\iota M_1(\mathrm{none})\circ(\text{algebraMap }\overline{\mathbb Q})$ agrees with the map $\overline{\mathbb Q}\to C\to\mathrm{Frac}$; the subfield of $\mathrm{Frac}$ generated by the image of $C$ together with the image of $\iota M_1(\mathrm{none})$ is the Mumford invariant field of $\Gamma_1(\mathrm{none})$ acting on `HolRingOf ϖ₁ ρ₁`; $\iota M_1(\mathrm{none})$ carries finite $\overline{\mathbb Q}$-linearly independent families to $C$-linearly independent ones; and further clauses governing the compatibility of $\iota M_1$ with the Galois action, the involutions $W$ and the degeneracy maps of the tower, at the base object.
--
--   *Conclusion.* The predicate `DescentIntertwining` holds for the same parameters $r=q'$, $ir=1$, $irbar=0$ and the same tuple $(A_1,\rho_1,\varpi_1,\Gamma_1,w_1,\bar w_1,s_1,d_1,F_N,\mathbb T,\mathrm{gal}_N,\mathrm{gal}_T,W,WT,\chi_1,\iota M_1)$. Its first three conjuncts are the three conditions on $\chi_1$ just described: triviality on inertia, nontriviality at every Frobenius at $q'$, and the equivalence $\chi_1(\tau)=1\iff\tau$ fixes every $x$ in the residue field of $A_1$ with $x^{q'^2}=x$. Its fourth conjunct is the normalisation clause for every object $j$ of the tower: for all $j$ and all $z\in\overline{\mathbb Q}$, $\iota M_1\,j$ applied to the image of $z$ in $\mathbb T.\mathrm{objField}\,j$ equals the image of $z$ under $\overline{\mathbb Q}\to C\to\mathrm{Frac}$ of `HolRingOf ϖ₁ ρ₁`. The remaining conjuncts are likewise quantified over all objects $j$ of the tower, so that the conclusion asserts at every level of the Hecke tower what the hypothesis `hBase` asserts at the base object alone.
--
--   This is the inductive half of Čerednik's interchange for the Hecke tower of primes away from $qq'$: the $q'$-adic uniformisation datum relating the Shimura curve tower to Mumford's invariant fields of the groups $\Gamma_1(j)$ is promoted from the base level $N$, where it is assumed, to every level $N\ell$. It feeds the existence statement [`CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero), which produces a pair of interchanged Hecke towers of Shimura curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_descentIntertwining_of_base_one_zero.lean

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

theorem CerednikDrinfeld.descentIntertwining_of_base_one_zero

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

    (hgalφ : ∀ (α : HeckeTower.Arr q q') (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : FN), galT α.1 τ • 𝕋.φ α x = 𝕋.φ α (galN τ • x))
    (hWφ : ∀ (α : HeckeTower.Arr q q') (i : Fin 2) (x : FN), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x))
    (hdeg : ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α)
    (hBase : CerednikDrinfeld.DescentIntertwiningBase q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁) :
    CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁ := by sorry
