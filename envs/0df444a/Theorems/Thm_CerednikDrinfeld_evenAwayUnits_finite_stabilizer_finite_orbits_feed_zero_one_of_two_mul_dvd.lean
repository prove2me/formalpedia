-- Prove2me | Theorems.Thm_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_finite_orbits_feed_zero_one_of_two_mul_dvd
-- name    : CerednikDrinfeld.evenAwayUnits_finite_stabilizer_finite_orbits_feed_zero_one_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/4632e21a-7d5d-5ed2-b2fe-d1c7ffeccf64
-- title:
--   Finite stabilisers and finitely many orbits for Γ₂ on the tree
-- statement:
--   The data are those of the Čerednik–Drinfeld frame on the $q$-side, and the conclusion concerns the action of the groups $\Gamma_2$ on the tree of $\mathcal{O}_0$-lattices.
--
--   **Arithmetic data.** A nonzero squarefree natural number $N$, primes $q$ and $q'$ with $q'\neq q$, with $\neg\,q\mid N$ (`hqN`), $\neg\,q'\mid N$ (`hq'N`), and $5\le q$, $5\le q'$ (`hq5`, `hq'5`); a nonzero natural number $D$ with $2Nqq'\mid D$ (`hD`).
--
--   **The definite side.** Rationals $a_1,b_1$ such that `hdef₁` holds for $q'$: $a_1<0$, $b_1<0$, and for every finite place $v$ of $\mathbb{Q}$ every nonzero element of $B_1\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q'$ lies in $v$, where $B_1=\mathbb{H}[\mathbb{Q},a_1,b_1]$. Two $\mathbb{Z}$-submodules $\Lambda_1,R_1$ of $B_1$ with $\Lambda_1$ a maximal order (an order not properly contained in another order, `hΛ₁`), $R_1$ an Eichler order of level $N$, i.e. an intersection of two maximal orders whose relative index in the first is $N$ (`hR₁`), and $R_1\le\Lambda_1$ (`hRΛ₁`). A unit $n_1$ of $B_1\otimes_{\mathbb{Q}}\mathbb{A}^{\mathrm{fin}}_{\mathbb{Q}}$ lying in `primeHeckeSet R₁ q`: $n_1$ lies in the finite adelic box of $R_1$ and $q\,n_1^{-1}$ lies in it, while $n_1^{-1}$ and $q^{-1}n_1$ do not (`hn₁`). Writing $S_1=R_1\sqcap\,^{n_1}R_1$ for `meetOrder R₁ n₁`, the hypotheses require $S_1$ to be an Eichler order of level $Nq$ (`hS₁`), conjugation by $n_1$ to preserve $S_1$ (`hnorm₁`), and the shift by $n_1$ on the class set of the finite-idele stabiliser of $S_1$ to be an involution (`hsq₁`); the class sets of the stabilisers of $S_1$ and of $R_1$ are finite. Finally `hlaws₁` is `ClassSetHeckeLaws N q Λ₁ R₁ n₁`: the edge Hecke matrices pairwise commute, the vertex Hecke matrices pairwise commute, the two degeneracy maps intertwine edge and vertex Hecke operators at every prime other than $q$, and the joint kernel of the degeneracy maps is stable under every edge Hecke operator.
--
--   **The indefinite side.** Rationals $a,b$ with `hB`: $0<a$ or $0<b$, and for every finite place $v$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; and a maximal order $\Lambda$ in $\mathbb{H}[\mathbb{Q},a,b]$ (`hΛ`).
--
--   **The characteristic-zero moduli frame over $\mathbb{Z}[1/D]$.** A field $\bar F$ over $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ (principal divisors exist, residue fields are finite-dimensional, $\Omega^1$ free of rank one) and essentially of finite type; a scheme $X$ with $\pi_X:X\to\operatorname{Spec}\mathbb{Z}[1/D]$ and a point $\bar s:\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}\mathbb{Z}[1/D]$; an assignment `pt` sending each ring $S$, each $S$-point $s$ of $\operatorname{Spec}\mathbb{Z}[1/D]$ and each fake elliptic curve for $\Lambda$ of level $N$ over $S$ to a morphism to $X$ over $s$, subject to `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective`, which are the clauses of `IsCoarseModuli` other than the universal property: constancy on isomorphism classes, compatibility with base change along ring homomorphisms, and surjectivity and injectivity up to isomorphism on points with values in algebraically closed fields. A curve model $\mathfrak{M}$ of $\bar F$ over $\overline{\mathbb{Q}}$, an isomorphism $e_{\mathfrak{M}}$ from $\mathfrak{M}.C$ to the fibre product of $\pi_X$ and $\bar s$ with $e_{\mathfrak{M}}$ followed by the second projection equal to $\mathfrak{M}.\mathrm{toBase}$ (`he𝔐`); a homomorphism `gal` from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the semilinear automorphisms of $\bar F$; tower data $\mathbb{T}$ for $(q,q')$ over $\bar F$ with Galois homomorphisms `galT` for each prime $\ell\neq q,q'$, two semilinear automorphisms $W$ of $\bar F$ and two $W_{\mathbb{T}}$ of each tower field; and a witness `tw` of `ModuliTowerWitnessD`, which packages place-indexed representatives of fake elliptic curves with and without extra $\ell$-level, their compatibility with `pt`, $e_{\mathfrak{M}}$ and the degeneracy maps of the tower, and the requirement that `gal`, `galT` induce the given automorphism of $\overline{\mathbb{Q}}$ while $W$, $W_{\mathbb{T}}$ induce the identity (summarised here).
--
--   **Local data at $q$.** A valuation subring $A_2$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A_2$ (`hA₂`), whose decomposition subgroup over $\mathbb{Q}$ acts by isometries for the valuation of $A_2$ (`hiso₂`); a finite place $v_2$ of $\mathbb{Q}$ containing $q$ (`hv₂`). Write $K_2$ for [`ValuationSubring.ratClosure A₂`](def/ValuationSubring_CompletionRatClosure.html#L13), the topological closure of the prime subfield inside the completion of $\overline{\mathbb{Q}}$ for the valuation of $A_2$. An injective $\mathbb{Q}$-algebra homomorphism $\iota_2:B_1\to M_2(K_2)$ (`hι₂`) and a homomorphism $\rho_2:B_1^\times\to \mathrm{PGL}_2(K_2)$ given on each unit by the projective class of its image under $\iota_2$ (`hρ₂`). A pseudo-uniformiser $\varpi_2$ of $K_2$ relative to the completion whose image in the completion is $q$ (`hϖ₂`), and the assumption that `Omega.HolRingOf ϖ₂ ρ₂` is a domain (`hdom₂`). A homomorphism $dIso_2$ from the decomposition subgroup to the isometric automorphisms of the completion, realising the Galois action (`hdIso₂`), and a character $\chi$ of the decomposition subgroup with values in $\mathbb{Z}/2$, trivial on inertia (`hχ₁`), nontrivial on any Frobenius at $q$ (`hχ₂`), and whose kernel consists of the elements fixing every element $x$ of the residue field of $A_2$ with $x^{q^2}=x$ (`hχ₃`).
--
--   **Hecke elements and the groups $\Gamma_2$.** For each prime $\ell\neq q,q'$, a unit $s_2(\ell)$ of $B_1$ and a unit $sf_2(\ell)$ of $B_1\otimes_{\mathbb{Q}}\mathbb{A}^{\mathrm{fin}}_{\mathbb{Q}}$ such that (`hs₂`) the component of $sf_2(\ell)$ at every finite place not containing $q$ is $s_2(\ell)\otimes 1$, its component at the places containing $q$ is $1$, the product of the diagonal idele of $\ell$ with $sf_2(\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ S₁ ℓ` if $\ell\mid N$ and in `primeHeckeSet S₁ ℓ` otherwise, and the reduced norm of $s_2(\ell)$ is $\ell$. A family $\Gamma_2$ of subgroups of $B_1^\times$ indexed by `Option` of the primes away from $q,q'$, with $\Gamma_2(\mathrm{none})$ characterised (`hΓ₂0`) as the set of units $x$ lying in `CosetGraph.awayUnits R₁ v₂` — that is, whose image in $(B_1\otimes\mathbb{Q}_w)^\times$ lies in the subgroup generated by the local unit box of $R_1$ at $w$, for every finite place $w\neq v_2$ — and such that $\mathrm{ord}_q(\mathrm{nrd}(x))$ is even, and with $\Gamma_2(\mathrm{some}\,\ell)=\Gamma_2(\mathrm{none})\cap s_2(\ell)\,\Gamma_2(\mathrm{none})\,s_2(\ell)^{-1}$ (`hΓ₂ℓ`). Two further families $w_2,\bar w_2$ of units of $B_1$ with `hw₂`: $w_2(\mathrm{none})$ lies in `awayUnits R₁ v₂` and has reduced norm $q$, and for each $\ell$, $w_2(\mathrm{some}\,\ell)$ lies in `awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` and has reduced norm $q$; and `hwbar₂`: each $\bar w_2$ has reduced norm $q'$, its local image at places $w\neq v_2$ not containing $q'$ lies in the local unit box of $R_1$ (respectively of `meetOrder R₁ (sf₂ ℓ)`), and conjugation by it preserves the local boxes of $R_1$ (respectively `meetOrder R₁ (sf₂ ℓ)`) and of $\Lambda_1$ at every place $w\neq v_2$.
--
--   **Coefficient rings.** A characteristic-zero domain $\mathcal{O}_0$ which is a discrete valuation ring (`hdvr₀`) with an irreducible element $\pi$ (`hπ`), $\pi$-adically complete (`hcpl`), residue ring of cardinality $q$ (`hres`), with $(q)=(\pi)$ (`hunr`), and with $K_2$ as fraction field; a characteristic-zero domain $Onr$ over $\mathcal{O}_0$ with an $\mathcal{O}_0$-automorphism $Fr$, $\pi$-adically complete (`hOc`), with $(\pi)$ maximal (`hOm`), every element a root of a monic $\mathcal{O}_0$-polynomial modulo $\pi$ (`hOa`), every monic polynomial of positive degree having a root modulo $\pi$ (`hOcl`), and $Fr(x)\equiv x^q \pmod \pi$ (`hFr`). A homomorphism `vdet` from $\mathrm{GL}_2(K_2)$ to $\mathbb{Z}$ (written multiplicatively) characterised by `hvdet` as the $\pi$-valuation of the determinant, a ring homomorphism $\psi_0:Onr\to$ the completion with values of valuation at most $1$ (`hψ₀`) extending the structure map of $\mathcal{O}_0$ (`hψ₀𝒪`); furthermore $\pi$ maps to $\varpi_2.\varpi$ (`hπϖ`), $N$ is invertible in $\mathcal{O}_0$ (`hN₀`), the image of $\mathcal{O}_0$ in $K_2$ is exactly the set of elements of valuation at most $1$ (`h𝒪₀`), and for $x$ of valuation $<1$ and $y\neq 0$ some power of $v(x)$ is at most $v(y)$ (`hrk`).
--
--   **Integral moduli and Atkin–Lehner maps.** A scheme $\mathcal{X}_0$ with $f_0:\mathcal{X}_0\to\operatorname{Spec}\mathcal{O}_0$ and an assignment $pt_0$ making it a coarse moduli space, in the full sense of `IsCoarseModuli`, for fake elliptic curves for $\Lambda$ of level $N$ (`h𝒳₀`), with $\mathcal{X}_0$ integral and $f_0$ flat, separated, locally of finite type and quasi-compact; for each prime $\ell\neq q,q'$ a scheme $\mathcal{Y}_0(\ell)$ with $g_0(\ell)$ to $\operatorname{Spec}\mathcal{O}_0$ and $ptT_0(\ell)$ making it a coarse moduli space for such curves with extra $\ell$-level (`h𝒴₀`); two morphisms $d_{0}(\ell),d_{1}(\ell):\mathcal{Y}_0(\ell)\to\mathcal{X}_0$ over the base (`hd₀f`, `hd₁f`) which on moduli points forget the extra level (`hd₀`) and pass to the target of an $\ell$-level isogeny (`hd₁`); and endomorphisms $ar$, $arbar$ of $\mathcal{X}_0$ over the base (`harf`, `harbarf`) inducing on moduli points the Atkin–Lehner quotient at $q$ (`har`) and at $q'$ (`harbar`).
--
--   **Uniformisation data.** Maps $\Theta$ and $\Theta_T(\ell)$ sending, for each $\mathcal{O}_0$-algebra $B$ in which $\pi$ is nilpotent, a pair consisting of an $\mathcal{O}_0$-algebra homomorphism $Onr\to B$ and a Deligne datum over $B$ for the formal upper half plane, to a $B$-point of $\mathcal{X}_0$ over $\operatorname{Spec}\mathcal{O}_0$, respectively of $\mathcal{Y}_0(\ell)$. The hypothesis `hCD` has twelve clauses (summarised here): naturality of $\Theta$ and of each $\Theta_T(\ell)$ in $B$; invariance of $\Theta$ under the twisted action (`OmegaNr.IsTwistedAct` for $\pi$, $Onr$, $Fr$, `vdet`) of the image under $\iota_2$ of any $\gamma\in$ `awayUnits R₁ v₂`, and invariance of $\Theta_T(\ell)$ under that of any $\gamma$ in the intersection of `awayUnits R₁ v₂` with its conjugate by $s_2(\ell)$; over an algebraically closed field in which $\pi$ is nilpotent and for a fixed algebra map from $Onr$, surjectivity of $\Theta$ and of $\Theta_T(\ell)$ onto the points of $f_0$, respectively $g_0(\ell)$, with fibres exactly the orbits of the respective twisted actions; initiality of $\Theta$ and of $\Theta_T(\ell)$ among natural transformations invariant under those actions; compatibility of $\Theta_T(\ell)$ with $d_{0}(\ell)$, and with $d_{1}(\ell)$ through the twisted action of $s_2(\ell)$; and the identification of $ar$ with the Frobenius twist by $1$ on the first coordinate and of $arbar$ with the twisted action of $\bar w_2(\mathrm{none})$.
--
--   **Conclusion.** Let $T$ denote the set of vertices of the lattice tree of $\mathcal{O}_0$-lattices in $K_2^2$, that is, homothety classes of full $\mathcal{O}_0$-lattices, with its $\mathrm{PGL}_2(K_2)$-action. The conclusion is the conjunction of four assertions:
--
--   1. for every vertex $v\in T$, the set of $g\in\mathrm{PGL}_2(K_2)$ that lie in the image of $\Gamma_2(\mathrm{none})$ under $\rho_2$ and satisfy $g\cdot v=v$ is finite;
--
--   2. there is a finite set $S$ of vertices such that every vertex $v$ admits $g$ in the image of $\Gamma_2(\mathrm{none})$ under $\rho_2$ with $g\cdot v\in S$;
--
--   3. for every prime $\ell\neq q,q'$ and every vertex $v$, the set of $g$ lying in the image of $\Gamma_2(\mathrm{some}\,\ell)$ under $\rho_2$ with $g\cdot v=v$ is finite;
--
--   4. for every prime $\ell\neq q,q'$ there is a finite set $S$ of vertices such that every vertex $v$ admits $g$ in the image of $\Gamma_2(\mathrm{some}\,\ell)$ under $\rho_2$ with $g\cdot v\in S$.
--
--   This is the discreteness-and-cocompactness input for the Čerednik–Drinfeld uniformisation on the $q$-side: the even-norm part of the away-from-$v_2$ unit group of the Eichler order, and each of its level-$\ell$ congruence subgroups, acts on the Bruhat–Tits tree of $\mathcal{O}_0$-lattices with finite vertex stabilisers and finitely many vertex orbits. It is consumed by [`CerednikDrinfeld.exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_zero_one_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_mumfordEmbedding_of_cerednikDrinfeld_uniformization_zero_one_of_two_mul_dvd), where these two properties are what permits the quotient of the formal upper half plane to be realised as a Mumford curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_finite_orbits_feed_zero_one_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.evenAwayUnits_finite_stabilizer_finite_orbits_feed_zero_one_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    {a₁ b₁ : ℚ} (hdef₁ : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) q')
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

    (χ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (hχ₁ : ∀ τ : ↥(A₂.decompositionSubgroup ℚ), (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₂.inertiaSubgroupIn ℚ → χ τ = 1)
    (hχ₂ : ∀ φ : ↥(A₂.decompositionSubgroup ℚ), A₂.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q → χ φ ≠ 1)
    (hχ₃ : ∀ τ : ↥(A₂.decompositionSubgroup ℚ), χ τ = 1 ↔ ∀ x : IsLocalRing.ResidueField ↥A₂, x ^ (q ^ 2) = x → τ • x = x)

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀] (hdvr₀ : IsDiscreteValuationRing 𝒪₀)
    (π : 𝒪₀) (hπ : Irreducible π) (hcpl : IsAdicComplete (Ideal.span {π}) 𝒪₀) (hres : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q)
    (hunr : Ideal.span {((q : ℕ) : 𝒪₀)} = Ideal.span {π})
    [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₂)] [IsFractionRing 𝒪₀ ↥(ValuationSubring.ratClosure A₂)]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪₀ Onr] (Fr : Onr ≃ₐ[𝒪₀] Onr)
    (hOc : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
    (hOm : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
    (hOa : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hOcl : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ q ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₂) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ValuationSubring.ratClosure A₂)) = algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) π) ^ n)
    (ψ₀ : Onr →+* A₂.valuation.Completion)
    (hπϖ : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂) π = ϖ₂.ϖ) (hN₀ : IsUnit ((N : ℕ) : 𝒪₀))
    (h𝒪₀ : ∀ x : ↥(ValuationSubring.ratClosure A₂), x ∈ Set.range (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion x) ≤ 1)
    (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))
    (hrk : ∀ x y : A₂.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (𝒴₀ : HeckeTower.AwayPrime q q' → Scheme.{0}) (g₀ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝒴₀ ℓ ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g₀ ℓ))
    (h𝒴₀ : ∀ ℓ : HeckeTower.AwayPrime q q', IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴₀ ℓ) (g₀ ℓ) (ptT₀ ℓ))
    (d₀₀ d₁₀ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝒴₀ ℓ ⟶ 𝒳₀)
    (hd₀f : ∀ ℓ, d₀₀ ℓ ≫ f₀ = g₀ ℓ) (hd₁f : ∀ ℓ, d₁₀ ℓ ≫ f₀ = g₀ ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT₀ ℓ S s u).1 ≫ d₀₀ ℓ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT₀ ℓ S s u).1 ≫ d₁₀ ℓ = (pt₀ S s d).1)

    (ar arbar : 𝒳₀ ⟶ 𝒳₀) (harf : ar ≫ f₀ = f₀) (harbarf : arbar ≫ f₀ = f₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q' E E' → (pt₀ S s E).1 ≫ arbar = (pt₀ S s E').1)

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints f₀).obj B)
    (ΘT : ∀ ℓ : HeckeTower.AwayPrime q q', ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints (g₀ ℓ)).obj B)
    (hCD :

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), Θ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints f₀).map φ (Θ B hB x)) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ΘT ℓ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints (g₀ ℓ)).map φ (ΘT ℓ B hB x))) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → Θ B hB x' = Θ B hB x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom) →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ΘT ℓ B hB x' = ΘT ℓ B hB x)) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints f₀).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, Θ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
            ∃ γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) (ψ, P) (ψ, P')) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints (g₀ ℓ)).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, ΘT ℓ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π).obj k, ΘT ℓ k hk (ψ, P) = ΘT ℓ k hk (ψ, P') ↔
            ∃ γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) (ψ, P) (ψ, P'))) ∧

      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u' B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u' B hB (Θ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints f₀).obj B), u' B hB y = u B hB y) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂).map (MulAut.conj (s₂ ℓ)).toMonoidHom) →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B hB y = u B hB y)) ∧

      (∀ (ℓ : HeckeTower.AwayPrime q q') (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₀₀ ℓ) (hd₀f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (s₂ ℓ)) x' x →
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₁₀ ℓ) (hd₁f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x') ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
        (Scheme.nilpPoints.mapHom f₀ f₀ ar harf).app B (Θ B hB x) = Θ B hB (FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) (wbar₂ none)) x x' →
        (Scheme.nilpPoints.mapHom f₀ f₀ arbar harbarf).app B (Θ B hB x) = Θ B hB x'))
    :
    (∀ v : LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂), Set.Finite {g : PGL(2, ↥(ValuationSubring.ratClosure A₂)) | g ∈ (Γ₂ none).map ρ₂ ∧ g • v = v}) ∧
    (∃ S : Finset (LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂)), ∀ v : LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂), ∃ g ∈ (Γ₂ none).map ρ₂, g • v ∈ S) ∧
    (∀ (i : (HeckeTower.AwayPrime q q')) (v : LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂)), Set.Finite {g : PGL(2, ↥(ValuationSubring.ratClosure A₂)) | g ∈ ((fun ℓ => Γ₂ (some ℓ)) i).map ρ₂ ∧ g • v = v}) ∧
    (∀ i : (HeckeTower.AwayPrime q q'), ∃ S : Finset (LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂)), ∀ v : LT.LatticeTree.Vertex 𝒪₀ ↥(ValuationSubring.ratClosure A₂), ∃ g ∈ ((fun ℓ => Γ₂ (some ℓ)) i).map ρ₂, g • v ∈ S) := by sorry
