-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd
-- name    : CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/2a7aec94-83b4-5bdb-a1e7-c76f02657caf
-- title:
--   Čerednik descent datum at q' from a moduli tower witness
-- statement:
--   Fix a non-zero squarefree integer $N$ and two distinct primes $q,q'$, neither dividing $N$, both at least $5$, together with a natural number $D$ divisible by $2Nqq'$.
--
--   **The place over $q'$.** Let $A_1$ be a valuation subring of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$ with `A₁.LiesOverPrime q'`, i.e. $q'$ is a non-unit of $A_1$, and assume (as a `Fact`) that `A₁.DecompositionIsometric ℚ` holds: every $\sigma$ in the decomposition subgroup of $A_1$ over $\mathbb Q$ satisfies $A_1.\mathrm{valuation}(\sigma x)=A_1.\mathrm{valuation}(x)$ for all $x\in\overline{\mathbb Q}$. Let $v_1$ be a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q'$.
--
--   **The definite side.** Let $a_2,b_2\in\mathbb Q$ satisfy `IsDefiniteRamifiedExactlyAt q`, that is $a_2<0$, $b_2<0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra precisely when $q\in v$. Let $\Lambda_2,R_2\subseteq \mathbb H[\mathbb Q,a_2,b_2]$ be $\mathbb Z$-submodules with $\Lambda_2$ a maximal order (an order maximal among orders), $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders whose relative index in the first is $N$) and $R_2\le\Lambda_2$. Let $n_2$ be a unit of $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ lying in `primeHeckeSet R₂ q'`: $n_2$ lies in the finite adelic box of $R_2$, so does $q'\,n_2^{-1}$, while $n_2^{-1}$ and $q'^{-1}n_2$ do not. It is assumed that `meetOrder R₂ n₂` $=R_2\cap n_2R_2n_2^{-1}$ is an Eichler order of level $Nq'$ (`hS₂`), that conjugation by $n_2$ fixes this order (`hnorm₂`), and that the shift $x\mapsto \mathrm{mk}(x_{\mathrm{out}}n_2)$ on the class set of the finite idele stabiliser of `meetOrder R₂ n₂` is an involution (`hsq₂`); the two class sets occurring are assumed finite, with decidable equality where needed. Finally `hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂` records four laws: the edge Hecke matrices `classSetEdgeHecke N q' Λ₂ R₂ n₂ ℓ` commute pairwise, the vertex Hecke matrices `classSetVertexHecke N Λ₂ ℓ` commute pairwise, for every prime $\ell\ne q'$ and each $i\in\{0,1\}$ the $i$-th joint degeneracy map of `classSetDegeneracyData R₂ n₂` intertwines the edge and vertex Hecke operators, and the joint kernel of the degeneracy maps is stable under every edge Hecke operator.
--
--   **The indefinite side.** Let $a,b\in\mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, that is $0<a$ or $0<b$, and $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra precisely when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order in it.
--
--   **The moduli package over $\mathbb Z[1/D]$.** Let $\bar F$ be a field over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors exist, all residue fields of places are finite over $\overline{\mathbb Q}$, and $\Omega_{\bar F/\overline{\mathbb Q}}$ is free of rank one) and is essentially of finite type. Let $X$ be a scheme with a morphism $\pi_X$ to $\operatorname{Spec}$ of `Localization.Away ((D : ℕ) : ℤ)`, let $\bar s$ be a $\overline{\mathbb Q}$-point of that base, and let `pt` assign to every commutative ring $S$, every $S$-point $s$ of the base and every fake elliptic curve $E$ in `FakeEllipticCurve Λ N S` a morphism to $X$ over $s$. Four hypotheses constrain `pt`: `pt_iso`, that isomorphic fake elliptic curves have the same image; `pt_pullback`, that for a ring homomorphism $\varphi:S\to S'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and $E,E'$ with `FakeEllipticCurve.IsPullback φ E E'`, the morphism attached to $E'$ is $\operatorname{Spec}\varphi$ followed by the one attached to $E$; `pt_surjective` and `pt_injective`, that over an algebraically closed field $k$ the map induced by `pt` on isomorphism classes of fake elliptic curves is onto the $k$-points of $X$ over $s$ and injective up to isomorphism.
--
--   Let $\mathfrak M$ be a `CurveModel` over $\overline{\mathbb Q}$ with function field $\bar F$ (a proper, smooth relative dimension one integral scheme with an identification of $\bar F$ with its function field and a bijection between closed points and places), let $e_{\mathfrak M}:\mathfrak M.C\to \pi_X\times_{\bar s}$ be an isomorphism with $e_{\mathfrak M}$ followed by the second projection equal to $\mathfrak M.\mathrm{toBase}$, and let $\mathrm{gal}$ be a homomorphism from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to the semilinear automorphisms of $\bar F$ over $\overline{\mathbb Q}$.
--
--   **The tower.** Let $\mathbb T$ be a `HeckeTower.TowerData q q' Fbar`: a field $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$ for each prime $\ell\notin\{q,q'\}$, each a curve over $\overline{\mathbb Q}$ and essentially of finite type, with $\overline{\mathbb Q}$-algebra maps $\varphi_\alpha:\bar F\to\mathbb T.F(\alpha_1)$ for the two arrows above each $\ell$, finite and integral. Let $\mathrm{galT}$ give semilinear Galois actions on each $\mathbb T.F(\ell)$, and let $W:\mathrm{Fin}\,2\to$ semilinear automorphisms of $\bar F$ and $WT(\ell):\mathrm{Fin}\,2\to$ semilinear automorphisms of $\mathbb T.F(\ell)$ be given. The hypothesis `tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT` asserts that these data are realised by the moduli problem: representatives `rep` of the places of $\bar F$ by fake elliptic curves over $\overline{\mathbb Q}$ whose `pt`-image is the corresponding closed point of $\mathfrak M.C$ transported by $e_{\mathfrak M}$, representatives `repT` of the places of $\mathbb T.F(\ell)$ by fake elliptic curves with extra level-$\ell$ structure, bijective on isomorphism classes, the conditions that $\mathrm{gal}$ and $\mathrm{galT}$ induce on $\overline{\mathbb Q}$ the given automorphism and that $W$, $WT$ act trivially on $\overline{\mathbb Q}$, the level-restriction compatibility of `repT` along $\varphi_{(\ell,0)}$, and the remaining fields of the structure expressing the corresponding compatibilities of the degeneracy arrows and of the actions $\mathrm{gal}$, $\mathrm{galT}$, $W$, $WT$.
--
--   **Mumford-side data at $A_1$.** Let $\iota_1:\mathbb H[\mathbb Q,a_2,b_2]\to M_2(\mathrm{ratClosure}\,A_1)$ be an injective $\mathbb Q$-algebra map into the $2\times2$ matrices over the topological closure of $\bot$ in the completion of $A_1$'s valuation, and let $\rho_1:\mathbb H[\mathbb Q,a_2,b_2]^\times\to \mathrm{PGL}_2(\mathrm{ratClosure}\,A_1)$ be the projectivisation of $\iota_1$ on units (`hρ₁`). Let $\varpi_1$ be a pseudo-uniformiser of $\mathrm{ratClosure}\,A_1$ in the completion with image $q'$ (`hϖ₁`), and assume `Omega.HolRingOf ϖ₁ ρ₁` is a domain.
--
--   Let $s_1(\ell)\in\mathbb H[\mathbb Q,a_2,b_2]^\times$ and $sf_1(\ell)$ adelic units be given for each prime $\ell\notin\{q,q'\}$, subject to `hs₁`: at every height-one prime $u$ not containing $q'$ the component of $sf_1(\ell)$ is $s_1(\ell)\otimes1$; at every $u$ containing $q'$ it is $1$; the product of the diagonal idele of $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise; and $\mathrm{nrd}(s_1(\ell))=\ell$.
--
--   Let $\Gamma_1$ assign a subgroup of $\mathbb H[\mathbb Q,a_2,b_2]^\times$ to each object of the tower, with $\Gamma_1(\mathrm{none})$ consisting exactly of the units lying in `CosetGraph.awayUnits R₂ v₁` (the intersection over all $w\ne v_1$ of the preimages under localisation at $w$ of the subgroup generated by the local box units of $R_2$) whose reduced norm has even $q'$-adic valuation (`hΓ₁0`), and $\Gamma_1(\mathrm{some}\ \ell)=\Gamma_1(\mathrm{none})\cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$ (`hΓ₁ℓ`).
--
--   Let $w_1,\bar w_1$ assign a unit of $\mathbb H[\mathbb Q,a_2,b_2]$ to each object of the tower. The hypothesis `hw₁` requires $w_1(\mathrm{none})\in$ `awayUnits R₂ v₁` with $\mathrm{nrd}=q'$, and $w_1(\mathrm{some}\ \ell)\in$ `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with $\mathrm{nrd}=q'$. The hypothesis `hwbar₁` requires $\mathrm{nrd}(\bar w_1(\mathrm{none}))=q$, that at every height-one prime $u\ne v_1$ not containing $q$ the local image of $\bar w_1(\mathrm{none})$ lies in the local box units of $R_2$ at $u$, and that at every $u\ne v_1$ conjugation by $\bar w_1(\mathrm{none})$ preserves, as an equivalence, membership in the local box of $R_2$ at $u$ and in the local box of $\Lambda_2$ at $u$; and the same three conditions for each $\bar w_1(\mathrm{some}\ \ell)$, with `meetOrder R₂ (sf₁ ℓ)` in place of $R_2$.
--
--   Finally let $\mathrm{dIso}_1$ be a homomorphism from the decomposition subgroup of $A_1$ over $\mathbb Q$ to the isometric automorphisms of the completion over $\mathrm{ratClosure}\,A_1$, realising the action: $(\mathrm{dIso}_1\tau)(x)=\tau\cdot x$ for all $x$ in the completion (`hdIso₁`).
--
--   **Conclusion.** There exist a homomorphism $\chi_1$ from the decomposition subgroup of $A_1$ over $\mathbb Q$ to $\mathrm{Multiplicative}(\mathbb Z/2)$ and, for every object $j$ of the tower, a ring homomorphism $\iota M_1(j):\mathbb T.\mathrm{objField}(j)\to\mathrm{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ such that
--   $$\mathrm{DescentIntertwiningBase}\ q'\ 1\ 0\ A_1\ \rho_1\ \varpi_1\ \Gamma_1\ w_1\ \bar w_1\ s_1\ \mathrm{dIso}_1\ \bar F\ \mathbb T\ \mathrm{gal}_0\ \mathrm{galT}_0\ W\ WT\ \chi_1\ \iota M_1$$
--   holds, where $\mathrm{gal}_0$ and $\mathrm{galT}_0(\ell)$ are the restrictions of $\mathrm{gal}$ and $\mathrm{galT}(\ell)$ to the decomposition subgroup, and the residue parameter is $r=q'$ with distinguished indices $1$ and $0$ in $\mathrm{Fin}\,2$. Unfolded, this predicate asserts: $\chi_1$ is trivial on the inertia subgroup of $A_1$ in $\mathbb Q$; $\chi_1(\varphi)\ne1$ for every $\varphi$ with `A₁.IsFrobeniusAt φ q'`; $\chi_1(\tau)=1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2}=x$; $\iota M_1(\mathrm{none})$ agrees on $\overline{\mathbb Q}$-scalars with the composite of $\overline{\mathbb Q}\to A_1.\mathrm{valuation}.\mathrm{Completion}$ and the structure map to the fraction field; the subfield generated by the image of the completion together with the image of $\iota M_1(\mathrm{none})$ equals `Mumford.invariantFieldOf` of the completion for the group $\Gamma_1(\mathrm{none})$ acting on $\mathrm{HolRingOf}\ \varpi_1\ \rho_1$; $\iota M_1(\mathrm{none})$ carries finite $\overline{\mathbb Q}$-linearly independent families in $\mathbb T.\mathrm{objField}(\mathrm{none})$ to families linearly independent over the completion; and the further clauses of the predicate, which involve the action of the decomposition subgroup through $\mathrm{dIso}_1$ on the fields $\mathbb T.\mathrm{objField}(j)$ together with the data $W$, $WT$, $w_1$, $\bar w_1$, $s_1$ at the levels of the tower.
--
--   This is the Čerednik–Drinfeld uniformisation step for the Shimura-curve tower of fake elliptic curves with $\Lambda$-action and level-$N$ structure, in the form needed for descent at the place above $q'$: from a moduli-theoretic witness for the tower over $\mathbb Z[1/D]$ it produces the quadratic character of the local decomposition group and the embeddings of the tower's function fields into the fraction field of the relevant holomorphic-functions ring. It is used by [`CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero), on the way to the local analysis of torsion on Shimura curves that underlies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd.lean

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
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    {a₂ b₂ : ℚ} (hdef₂ : IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q)
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

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

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
    :
    (∃ (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁)),
        CerednikDrinfeld.DescentIntertwiningBase q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
          Fbar 𝕋 (gal.comp (A₁.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₁.decompositionSubgroup ℚ).subtype) W WT χ₁ ιM₁) := by sorry
