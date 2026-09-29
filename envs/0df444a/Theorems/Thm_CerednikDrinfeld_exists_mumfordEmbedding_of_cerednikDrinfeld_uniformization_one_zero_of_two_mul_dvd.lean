-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_one_zero_of_two_mul_dvd
-- name    : CerednikDrinfeld.exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_one_zero_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/c39ffe9e-b46e-5c2a-9220-95f0ec13e1b5
-- title:
--   Mumford embedding from Čerednik–Drinfeld uniformisation
-- statement:
--   Throughout, $N$ is a non-zero squarefree natural number, $q$ and $q'$ are primes with $q\nmid N$, $q'\nmid N$, $q'\neq q$, both at least $5$, and $D$ is a non-zero natural number divisible by $2Nqq'$. Further, $A_1$ is a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` lying over $q'$, in the sense that $q'$ is a non-unit of $A_1$.
--
--   **Definite quaternionic data.** Rationals $a_2,b_2$ are given with `IsDefiniteRamifiedExactlyAt q`, i.e. $a_2<0$, $b_2<0$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the algebra $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ has all non-zero elements invertible exactly when $q\in v$. Inside $\mathbb H[\mathbb Q,a_2,b_2]$ are a maximal order $\Lambda_2$ and an order $R_2\le\Lambda_2$ which is Eichler of level $N$ (an intersection of two maximal orders of relative index $N$). A finite-idele unit $n_2$ lies in `primeHeckeSet R₂ q'` (its four conditions on membership of the finite adelic box of $R_2$ of $n_2$, of $q'n_2^{-1}$, and non-membership of $n_2^{-1}$ and of $q'^{-1}n_2$), the order $\mathrm{meetOrder}\,R_2\,n_2=R_2\cap n_2R_2n_2^{-1}$ is Eichler of level $Nq'$ (`hS₂`), conjugation by $n_2$ fixes it (`hnorm₂`), and translation by $n_2$ on the class set of its finite-idele stabiliser is an involution (`hsq₂`); the relevant class sets are finite. The hypothesis `hlaws₂` is `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, the two degeneracy pushforwards intertwine edge and vertex Hecke operators at primes other than $q'$, and the joint kernel of the degeneracy maps is stable under all edge Hecke operators.
--
--   **Indefinite quaternionic data.** Rationals $a,b$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, namely $0<a$ or $0<b$, and a height-one prime $v$ is ramified exactly when $q\in v$ or $q'\in v$; $\Lambda$ is a maximal order in $\mathbb H[\mathbb Q,a,b]$.
--
--   **Curve and moduli data over $\mathbb Z[1/D]$.** $\bar F=$ `Fbar` is a field extension of $\overline{\mathbb Q}$ which is a curve field over it (principal divisors, finite residue extensions, Kähler differentials free of rank one) and essentially of finite type. A scheme $X$ is given over $\operatorname{Spec}$ of `Localization.Away ((D : ℕ) : ℤ)`, together with a $\overline{\mathbb Q}$-point $\bar s$ of that base and a family `pt` attaching to each fake elliptic curve for $(\Lambda,N)$ over a ring $S$ a section of $\pi_X$ over the given $S$-point. The hypotheses `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective` are the four point-level coarse-moduli axioms: invariance under isomorphism of fake elliptic curves, compatibility with base change along ring maps, and surjectivity and injectivity up to isomorphism on points valued in algebraically closed fields (no universal property is assumed here). A curve model $\mathfrak M$ of $\bar F$ over $\overline{\mathbb Q}$ is given with an isomorphism $e_{\mathfrak M}$ onto the pullback of $\pi_X$ along $\bar s$, compatible with the structure morphisms ($e_{\mathfrak M}$ followed by the second projection is $\mathfrak M.\mathrm{toBase}$), a Galois action `gal` of $\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ by semilinear automorphisms of $\bar F$, tower data $\mathbb T$ of Hecke type for the primes away from $q,q'$ with Galois actions `galT` on its fields, and semilinear involutive data $W\colon \mathrm{Fin}\,2\to$ `SemilinearAut` on $\bar F$ and $W_T$ on the tower fields; `tw` is a witness of type `ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT`, tying places of $\bar F$ and of the tower fields to fake elliptic curves with and without extra level, and the Galois and $W$ actions to that dictionary.
--
--   **Local data at $q'$.** The decomposition subgroup of $A_1$ over $\mathbb Q$ acts isometrically for the valuation of $A_1$; $v_1$ is a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q'$. An injective $\mathbb Q$-algebra map $\iota_1$ embeds $\mathbb H[\mathbb Q,a_2,b_2]$ into $2\times 2$ matrices over [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13) (the closure of the prime subfield in the completion $C=A_1.\mathrm{valuation.Completion}$), and $\rho_1$ is the induced projective representation on $\mathrm{PGL}_2$, given on units by $\iota_1$ (`hρ₁`). A pseudo-uniformiser $\varpi_1$ of `ratClosure A₁` in $C$ is fixed whose image in $C$ is $q'$ (`hϖ₁`), and the holomorphic ring `HolRingOf ϖ₁ ρ₁` (functions on the upper half plane holomorphic on each affinoid, carrying the $\mathbb H^\times$-action through $\rho_1$) is assumed to be a domain.
--
--   **Hecke elements and discrete groups.** For each prime $\ell\neq q,q'$ an element $s_1(\ell)\in\mathbb H[\mathbb Q,a_2,b_2]^\times$ and a finite-idele unit $sf_1(\ell)$ are given with `hs₁`: at primes not containing $q'$ the local component of $sf_1(\ell)$ is $s_1(\ell)\otimes 1$, at primes containing $q'$ it is $1$, the product of the diagonal idele of $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` when $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise, and the reduced norm of $s_1(\ell)$ is $\ell$. Subgroups $\Gamma_1$ indexed by `HeckeTower.Obj q q'` are prescribed by `hΓ₁0`, $\Gamma_1(\mathrm{none})$ consisting of those units lying in `CosetGraph.awayUnits R₂ v₁` (locally in the unit box of $R_2$ at every height-one prime other than $v_1$) whose reduced norm has even $q'$-adic valuation, and by `hΓ₁ℓ`, $\Gamma_1(\ell)=\Gamma_1(\mathrm{none})\cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$. Elements $w_1,\bar w_1$ indexed likewise satisfy `hw₁`: $w_1(\mathrm{none})$ lies in `awayUnits R₂ v₁` with reduced norm $q'$, and $w_1(\ell)$ lies in `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; and `hwbar₁`: $\bar w_1(\mathrm{none})$ has reduced norm $q$, is a local unit of $R_2$ at every prime $u\neq v_1$ not containing $q$, and conjugation by it preserves both the local box of $R_2$ and that of $\Lambda_2$ at every $u\neq v_1$; the same conditions hold for $\bar w_1(\ell)$ with $R_2$ replaced by $\mathrm{meetOrder}\,R_2\,(sf_1(\ell))$. Moreover $d\mathrm{Iso}_1$ realises the decomposition subgroup by isometric automorphisms of $C$ inducing the Galois action (`hdIso₁`), and $\chi$ is a character of the decomposition subgroup with values in $\mathbb Z/2$ which is trivial on inertia (`hχ₁`), non-trivial at any Frobenius at $q'$ (`hχ₂`), and whose kernel consists exactly of those elements fixing all elements of the residue field of $A_1$ satisfying $x^{q'^2}=x$ (`hχ₃`).
--
--   **Arithmetic base and unramified extension.** $\mathcal O_0$ is a characteristic-zero discrete valuation domain with irreducible $\pi$, $\pi$-adically complete, residue field of cardinality $q'$ and $(\pi)=(q')$, equipped with an algebra structure making `ratClosure A₁` its fraction field. $O^{\mathrm{nr}}$ is a characteristic-zero $\mathcal O_0$-domain with an $\mathcal O_0$-automorphism $\mathrm{Fr}$, complete for the ideal generated by $\pi$, with that ideal maximal, every element satisfying a monic polynomial over $\mathcal O_0$ modulo $\pi$, every non-constant monic polynomial having a root modulo $\pi$, and $\mathrm{Fr}(x)\equiv x^{q'}$ modulo $\pi$. A homomorphism $v\!\det$ from $\mathrm{GL}_2(\mathrm{ratClosure}\,A_1)$ to $\mathbb Z$ is characterised by `hvdet` through the determinant up to units times a power of $\pi$. Finally $\psi_0\colon O^{\mathrm{nr}}\to C$ is a ring map, $\pi$ maps to $\varpi_1.\varpi$ (`hπϖ`), $N$ is a unit of $\mathcal O_0$ (`hN₀`), the image of $\mathcal O_0$ in `ratClosure A₁` is exactly the set of elements of valuation at most $1$ (`h𝒪₀`), $\psi_0$ takes values of valuation at most $1$ (`hψ₀`), $\psi_0$ restricts to the structure map on $\mathcal O_0$ (`hψ₀𝒪`), and `hrk` states that for $x$ of valuation $<1$ and $y\neq 0$ in $C$ some power of $v(x)$ is at most $v(y)$.
--
--   **Integral moduli over $\mathcal O_0$.** A scheme $\mathcal X_0$ with $f_0\colon\mathcal X_0\to\operatorname{Spec}\mathcal O_0$ and a point family $\mathrm{pt}_0$ is a coarse moduli space `IsCoarseModuli Λ N 𝒳₀ f₀ pt₀` (the four point-level axioms together with the universal property), with $\mathcal X_0$ integral and $f_0$ flat, separated, locally of finite type and quasi-compact. For each prime $\ell$ away from $q'$ and $q$, a scheme $\mathcal Y_0(\ell)$ with $g_0(\ell)$ and $\mathrm{pt}_{T,0}(\ell)$ is a coarse moduli space for fake elliptic curves with extra $\ell$-level (`h𝒴₀`), and $d_{0},d_{1}\colon\mathcal Y_0(\ell)\to\mathcal X_0$ are morphisms over the base (`hd₀f`, `hd₁f`) realising on points the forgetting of the extra level (`hd₀`) and the passage to the $\ell$-isogenous quotient (`hd₁`, for any $d$ with `FakeEllipticCurve.IsLevelIsogeny ℓ u d`). Morphisms $a_r,\bar a_r$ of $\mathcal X_0$ over the base (`harf`, `harbarf`) realise on points the Atkin–Lehner quotients at $q'$ (`har`) and at $q$ (`harbar`).
--
--   **Uniformisation data.** Families $\Theta$ and $\Theta_T(\ell)$ send, for every $\mathcal O_0$-algebra $B$ in which $\pi$ is nilpotent, a point of the product functor $\mathrm{Hom}_{\mathcal O_0}(O^{\mathrm{nr}},-)\times\Omega$ (Deligne data on the lattice tree) to a nilpotent point of $f_0$, resp. of $g_0(\ell)$. The hypothesis `hCD` is a twelve-fold conjunction: naturality of $\Theta$ and of each $\Theta_T(\ell)$ in $B$; invariance of $\Theta$ under the twisted action `FormalOmega.OmegaNr.IsTwistedAct` of $\iota_1(\gamma)$ for $\gamma\in$ `awayUnits R₂ v₁`, and of $\Theta_T(\ell)$ for $\gamma$ in the intersection of that group with its conjugate by $s_1$ at the prime $\ell$ (indices transposed between `AwayPrime q' q` and `AwayPrime q q'`); for every algebraically closed $\mathcal O_0$-algebra field $k$ with $\pi$ nilpotent and every $\mathcal O_0$-algebra map $\psi\colon O^{\mathrm{nr}}\to k$, surjectivity of $P\mapsto\Theta(\psi,P)$ onto nilpotent points of $f_0$ over $k$ together with the description of its fibres as orbits of the twisted action of `awayUnits R₂ v₁`, and the analogous statement for each $\Theta_T(\ell)$ with the intersected group; the universal property of $\Theta$, resp. of each $\Theta_T(\ell)$, as a formal categorical quotient, asserting for each $T\to\operatorname{Spec}\mathcal O_0$ and each natural invariant family $\rho$ the existence of a unique natural transformation $u$ on nilpotent points with $u\circ\Theta=\rho$; compatibility of $\Theta_T(\ell)$ with $d_{0}$; compatibility with $d_{1}$, where the twisted action of $\iota_1(s_1(\ell))$ carries $x'$ to $x$; the identity expressing $a_r$ as the Frobenius twist `FormalOmega.frobTwist Onr Fr 1` on the first coordinate; and the identity expressing $\bar a_r$ through the twisted action of $\iota_1(\bar w_1(\mathrm{none}))$.
--
--   **Conclusion.** There exists a ring homomorphism $\iota_0\colon\bar F\to\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ such that:
--
--   1. for every $z\in\overline{\mathbb Q}$, $\iota_0$ of the image of $z$ in $\bar F$ equals the image of $z$ under $\overline{\mathbb Q}\to C\to\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$;
--
--   2. the subfield of $\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ generated by the image of $C$ together with the image of $\iota_0$ equals `Mumford.invariantFieldOf` of $C$, $\mathbb H[\mathbb Q,a_2,b_2]^\times$ and $\mathrm{HolRingOf}\ \varpi_1\ \rho_1$ for the subgroup $\Gamma_1(\mathrm{none})$, i.e. the field of $\Gamma_1(\mathrm{none})$-invariants;
--
--   3. for every finite subset $t$ of $\bar F$ whose elements are linearly independent over $\overline{\mathbb Q}$, their images under $\iota_0$ are linearly independent over $C$;
--
--   4. for every $\tau$ in the decomposition subgroup of $A_1$ over $\mathbb Q$ and every $x\in\bar F$, $\iota_0(\tau\cdot x)$, the action being that of `gal` composed with the inclusion of the decomposition subgroup, equals $1\cdot$ or $w_1(\mathrm{none})\cdot$ applied to `Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (ι₀ x)`, according as $\chi(\tau)=1$ or not;
--
--   5. $\iota_0(W_1\cdot x)=w_1(\mathrm{none})\cdot\iota_0(x)$ for all $x\in\bar F$;
--
--   6. $\iota_0(W_0\cdot x)=\bar w_1(\mathrm{none})\cdot\iota_0(x)$ for all $x\in\bar F$;
--
--   7. for every prime $\ell$ away from $q$ and $q'$ there is a ring homomorphism $\iota_\ell\colon\mathbb T.F(\ell)\to\operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ with $\iota_\ell(\mathbb T.\varphi(\ell,0)(x))=\iota_0(x)$ and $\iota_\ell(\mathbb T.\varphi(\ell,1)(x))=s_1(\ell)\cdot\iota_0(x)$ for all $x\in\bar F$.
--
--   This is the Čerednik–Drinfeld step of the Ribet level-lowering route: from the $q'$-adic uniformisation of the integral coarse moduli space of fake elliptic curves it produces a Mumford-style embedding of the function field of the geometric Shimura curve, and of the fields of the Hecke tower above it, into the fraction field of the ring of rigid-analytic functions on the Drinfeld upper half plane, equivariantly for the decomposition group at $q'$ and for the two Atkin–Lehner involutions. It is used by [`CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd), which packages these clauses into the descent intertwining base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_one_zero_of_two_mul_dvd.lean

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
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_one_zero_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
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

    (χ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (hχ₁ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χ τ = 1))
    (hχ₂ : (∀ φ : ↥(A₁.decompositionSubgroup ℚ), A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χ φ ≠ 1))
    (hχ₃ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χ τ = 1 ↔ ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x))

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀] (hdvr₀ : IsDiscreteValuationRing 𝒪₀)
    (π : 𝒪₀) (hπ : Irreducible π) (hcpl : IsAdicComplete (Ideal.span {π}) 𝒪₀) (hres : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q')
    (hunr : Ideal.span {((q' : ℕ) : 𝒪₀)} = Ideal.span {π})
    [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₁)] [IsFractionRing 𝒪₀ ↥(ValuationSubring.ratClosure A₁)]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪₀ Onr] (Fr : Onr ≃ₐ[𝒪₀] Onr)
    (hOc : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
    (hOm : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
    (hOa : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hOcl : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ q' ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ValuationSubring.ratClosure A₁)) = algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π) ^ n)
    (ψ₀ : Onr →+* A₁.valuation.Completion)
    (hπϖ : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π = ϖ₁.ϖ) (hN₀ : IsUnit ((N : ℕ) : 𝒪₀))
    (h𝒪₀ : ∀ x : ↥(ValuationSubring.ratClosure A₁), x ∈ Set.range (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion x) ≤ 1)
    (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))
    (hrk : ∀ x y : A₁.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (𝒴₀ : HeckeTower.AwayPrime q' q → Scheme.{0}) (g₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g₀ ℓ))
    (h𝒴₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴₀ ℓ) (g₀ ℓ) (ptT₀ ℓ))
    (d₀₀ d₁₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ 𝒳₀)
    (hd₀f : ∀ ℓ, d₀₀ ℓ ≫ f₀ = g₀ ℓ) (hd₁f : ∀ ℓ, d₁₀ ℓ ≫ f₀ = g₀ ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT₀ ℓ S s u).1 ≫ d₀₀ ℓ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT₀ ℓ S s u).1 ≫ d₁₀ ℓ = (pt₀ S s d).1)

    (ar arbar : 𝒳₀ ⟶ 𝒳₀) (harf : ar ≫ f₀ = f₀) (harbarf : arbar ≫ f₀ = f₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q' E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q E E' → (pt₀ S s E).1 ≫ arbar = (pt₀ S s E').1)

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints f₀).obj B)
    (ΘT : ∀ ℓ : HeckeTower.AwayPrime q' q, ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints (g₀ ℓ)).obj B)
    (hCD :

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), Θ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints f₀).map φ (Θ B hB x)) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ΘT ℓ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints (g₀ ℓ)).map φ (ΘT ℓ B hB x))) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → Θ B hB x' = Θ B hB x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ΘT ℓ B hB x' = ΘT ℓ B hB x)) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints f₀).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
            ∃ γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P')) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints (g₀ ℓ)).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = ΘT ℓ k hk (ψ, P') ↔
            ∃ γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P'))) ∧

      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u' B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (Θ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints f₀).obj B), u' B hB y = u B hB y) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B hB y = u B hB y)) ∧

      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₀₀ ℓ) (hd₀f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)) x' x →
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₁₀ ℓ) (hd₁f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x') ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom f₀ f₀ ar harf).app B (Θ B hB x) = Θ B hB (FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (wbar₁ none)) x x' →
        (Scheme.nilpPoints.mapHom f₀ f₀ arbar harbarf).app B (Θ B hB x) = Θ B hB x'))
    :
    ∃ ι₀ : Fbar →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁),
      (∀ z : AlgebraicClosure ℚ, ι₀ (algebraMap (AlgebraicClosure ℚ) Fbar z) =
          algebraMap A₁.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) ((z : AlgebraicClosure ℚ) : A₁.valuation.Completion)) ∧
      (Subfield.closure (Set.range (algebraMap A₁.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∪ Set.range ι₀) =
          Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none)) ∧
      (∀ t : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
          LinearIndependent A₁.valuation.Completion (fun x : t => ι₀ (x : Fbar))) ∧
      (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : Fbar),
          ι₀ ((gal.comp (A₁.decompositionSubgroup ℚ).subtype) τ • x) =
            (if χ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ none) •
              Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (ι₀ x)) ∧
      (∀ x : Fbar, ι₀ (W 1 • x) = w₁ none • ι₀ x) ∧
      (∀ x : Fbar, ι₀ (W 0 • x) = wbar₁ none • ι₀ x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ ιℓ : 𝕋.F ℓ →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁),
      (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 0) x) = ι₀ x) ∧ (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 1) x) = (s₁ ℓ) • ι₀ x)) := by sorry
