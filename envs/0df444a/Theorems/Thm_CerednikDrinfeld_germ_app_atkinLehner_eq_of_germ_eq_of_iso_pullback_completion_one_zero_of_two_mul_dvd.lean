-- Prove2me | Theorems.Thm_CerednikDrinfeld_germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd
-- name    : CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/b0125830-b894-54b5-824f-a8961a3cc3f9
-- title:
--   Atkin–Lehner equivariance of the pinned function-field embedding
-- statement:
--   Throughout, $C$ denotes the completion $A_1.\mathrm{valuation}.\mathrm{Completion}$ of the algebraic closure of $\mathbb{Q}$ at the valuation subring $A_1$, and $\mathcal{X}_C$ denotes the fibre product of $f_0 : \mathcal{X}_0 \to \operatorname{Spec}\mathcal{O}_0$ with $\operatorname{Spec}$ of the composite $\mathcal{O}_0 \to \mathrm{ratClosure}\,A_1 \to C$, where $\mathrm{ratClosure}\,A_1$ is the closure of the prime subfield in $C$.
--
--   **Numerical data.** Natural numbers $N \neq 0$ squarefree ($hN$), primes $q, q'$ with $q \nmid N$, $q' \nmid N$ ($hqN$, $hq'N$), $q' \neq q$ ($hqq'$), both at least $5$ ($hq5$, $hq'5$), and a non-zero $D$ divisible by $2Nqq'$ ($hD$). Further, a valuation subring $A_1$ of the algebraic closure of $\mathbb{Q}$ with $q'$ a non-unit of $A_1$ ($hA_1$, i.e. `A₁.LiesOverPrime q'`), a height-one prime $v_1$ of the integers of $\mathbb{Q}$ containing $q'$ ($hv_1$), and the assumption $hiso_1$ that the decomposition subgroup of $A_1$ over $\mathbb{Q}$ acts by isometries for the valuation of $A_1$.
--
--   **Definite quaternion data.** Rationals $a_2, b_2$ with $hdef_2$: $a_2 < 0$, $b_2 < 0$, and for a finite place $v$ of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a_2,b_2] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra precisely when $q$ lies in $v$; a maximal order $\Lambda_2$ ($h\Lambda_2$: an order maximal among orders containing it), an Eichler order $R_2$ of level $N$ ($hR_2$: an intersection of two maximal orders of relative index $N$ in the first) with $R_2 \le \Lambda_2$ ($hR\Lambda_2$); a finite-idele unit $n_2$ of $\mathbb{H}[\mathbb{Q},a_2,b_2]$ lying in `primeHeckeSet R₂ q'` ($hn_2$), such that the order $\mathrm{meetOrder}\,R_2\,n_2 = R_2 \cap n_2 R_2 n_2^{-1}$ is Eichler of level $Nq'$ ($hS_2$), is stable under conjugation by $n_2$ ($hnorm_2$), and such that the shift by $n_2$ on the class set of its finite-idele stabiliser is an involution ($hsq_2$); finally $hlaws_2 =$ `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`, the four assertions that the edge Hecke matrices commute pairwise, that the vertex Hecke matrices commute pairwise, that the two degeneracy pushforwards intertwine edge and vertex Hecke operators at primes other than $q'$, and that the joint kernel of the degeneracy pushforwards is preserved by every edge Hecke operator.
--
--   **Indefinite quaternion data and the moduli problem.** Rationals $a, b$ with $hB$: $0 < a$ or $0 < b$, and for a finite place $v$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra precisely when $v$ contains $q$ or $q'$; a maximal order $\Lambda$ ($h\Lambda$). A field $\bar F =$ `Fbar` over the algebraic closure of $\mathbb{Q}$ which is a curve over it (principal divisors of degree zero, finite residue extensions, and module of differentials free of rank one) and essentially of finite type. A scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}\mathbb{Z}[1/D]$, a point $\bar s$ of $\operatorname{Spec}\mathbb{Z}[1/D]$ with values in the algebraic closure of $\mathbb{Q}$, and an assignment $\mathrm{pt}$ sending a fake elliptic curve over a commutative ring $S$ with $\Lambda$-action and level-$N$ data to an $S$-point of $X$ over $s$; the four clauses $pt\_iso$ (isomorphic objects have the same point), $pt\_pullback$ (compatibility with base change along a ring map), $pt\_surjective$ and $pt\_injective$ (bijectivity on isomorphism classes over algebraically closed fields) are assumed, the universal property of a coarse moduli space not being assumed for $X$.
--
--   **The curve model and the tower.** A curve model $\mathfrak{M}$ over the algebraic closure of $\mathbb{Q}$ with function field identified with $\bar F$ (a smooth proper integral curve together with $\mathfrak{M}.\mathrm{ffEquiv}$, a bijection of its closed points with the places of $\bar F$, and the stalk–valuation-subring compatibility), a morphism $e_{\mathfrak{M}}$ from $\mathfrak{M}.C$ to the fibre product of $\pi_X$ and $\bar s$ which is an isomorphism and satisfies $e_{\mathfrak{M}}$ followed by the second projection equals $\mathfrak{M}.\mathrm{toBase}$ ($he_{\mathfrak{M}}$); a homomorphism $gal$ from $\operatorname{Gal}$ of the algebraic closure of $\mathbb{Q}$ to the semilinear automorphisms of $\bar F$; tower data $\mathbb{T}$ over $\bar F$ indexed by the primes away from $q, q'$, with Galois actions $galT$ on each member; two semilinear automorphisms $W_0, W_1$ of $\bar F$ and, for each $\ell$, two semilinear automorphisms $WT_\ell$ of $\mathbb{T}.F\,\ell$; and a witness $tw :$ `ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT` tying representing fake elliptic curves to places of $\bar F$ and of the tower fields, the base automorphisms of $gal$, $galT$, $W$ and $WT$, and the degeneracy and Atkin–Lehner relations in the tower.
--
--   **Local data at $q'$.** An injective $\mathbb{Q}$-algebra map $\iota_1$ from $\mathbb{H}[\mathbb{Q},a_2,b_2]$ into $2 \times 2$ matrices over $\mathrm{ratClosure}\,A_1$ ($h\iota_1$), the induced homomorphism $\rho_1$ to $\mathrm{PGL}_2$ ($h\rho_1$), a pseudo-uniformizer $\varpi_1$ whose image in $C$ is $q'$ ($h\varpi_1$), and the assumption $hdom_1$ that the ring of functions holomorphic on all affinoids attached to $\varpi_1, \rho_1$ is a domain. For each prime $\ell$ away from $q, q'$: a unit $s_1(\ell)$ of $\mathbb{H}[\mathbb{Q},a_2,b_2]$ and a finite idele $sf_1(\ell)$ with $hs_1$ asserting that $sf_1(\ell)$ has component $s_1(\ell) \otimes 1$ at places not containing $q'$, component $1$ at places containing $q'$, that the diagonal idele of $\ell$ times $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell \mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise, and that the reduced norm of $s_1(\ell)$ is $\ell$. Subgroups $\Gamma_1$ indexed by `Option` with $h\Gamma_10$: $\Gamma_1(\mathrm{none})$ consists of the units lying in `CosetGraph.awayUnits R₂ v₁` (locally in the closure of the unit box of $R_2$ at every place other than $v_1$) whose reduced norm has even $q'$-adic valuation, and $h\Gamma_1\ell$: $\Gamma_1(\mathrm{some}\,\ell)$ is the intersection of $\Gamma_1(\mathrm{none})$ with its conjugate by $s_1(\ell)$. Elements $w_1$, $\bar w_1$ indexed by `Option`, with $hw_1$: $w_1(\mathrm{none})$ lies in `awayUnits R₂ v₁` and has reduced norm $q'$, and $w_1(\mathrm{some}\,\ell)$ lies in `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; and $hwbar_1$: $\bar w_1(\mathrm{none})$ has reduced norm $q$, its local image lies in the local unit box of $R_2$ at every place $u \neq v_1$ not containing $q$, and conjugation by it preserves the local boxes of $R_2$ and of $\Lambda_2$ at every $u \neq v_1$, with the same conditions for $\bar w_1(\mathrm{some}\,\ell)$ with $\mathrm{meetOrder}\,R_2\,(sf_1(\ell))$ in place of $R_2$. A homomorphism $dIso_1$ from the decomposition subgroup to the isometric automorphisms of $C$ realising the Galois action ($hdIso_1$). A character $\chi$ of the decomposition subgroup with values in $\mathbb{Z}/2$, trivial on inertia ($h\chi_1$), non-trivial on every Frobenius at $q'$ ($h\chi_2$), and with kernel the elements fixing every element of the residue field of $A_1$ satisfying $x^{q'^2} = x$ ($h\chi_3$).
--
--   **The coefficient rings.** A discrete valuation ring $\mathcal{O}_0$ of characteristic zero ($hdvr_0$) with irreducible $\pi$ ($h\pi$), $\pi$-adically complete ($hcpl$), residue field of cardinality $q'$ ($hres$), with $q'$ generating the same ideal as $\pi$ ($hunr$), and with $\mathrm{ratClosure}\,A_1$ as fraction field; an $\mathcal{O}_0$-algebra $Onr$, a domain of characteristic zero, with an $\mathcal{O}_0$-algebra automorphism $Fr$, complete and local at $\pi$ ($hOc$, $hOm$), integral modulo $\pi$ ($hOa$), with every monic polynomial of positive degree having a root modulo $\pi$ ($hOcl$), and $Fr\,x \equiv x^{q'}$ modulo $\pi$ ($hFr$); a homomorphism $vdet$ from $\mathrm{GL}_2(\mathrm{ratClosure}\,A_1)$ to $\mathbb{Z}$ recording the $\pi$-valuation of the determinant ($hvdet$); a ring map $\psi_0 : Onr \to C$ together with $h\pi\varpi$ ($\pi$ is $\varpi_1.\varpi$), $hN_0$ ($N$ invertible in $\mathcal{O}_0$), $h\mathcal{O}_0$ (the image of $\mathcal{O}_0$ is exactly the set of elements of valuation at most one), $h\psi_0$ and $h\psi_0\mathcal{O}$ (integrality of $\psi_0$ and compatibility with $\mathcal{O}_0$), and $hrk$ (a rank-one comparison of valuations).
--
--   **Integral models.** An integral scheme $\mathcal{X}_0$ with $f_0 : \mathcal{X}_0 \to \operatorname{Spec}\mathcal{O}_0$ flat, separated, locally of finite type and quasi-compact, together with $\mathrm{pt}_0$ making $(\mathcal{X}_0, f_0, \mathrm{pt}_0)$ a coarse moduli space for fake elliptic curves with $\Lambda$-action and level-$N$ data ($h\mathcal{X}_0$, including the universal property). For each prime $\ell$ away from $q', q$: a scheme $\mathcal{Y}_0(\ell)$ with $g_0(\ell)$ to $\operatorname{Spec}\mathcal{O}_0$ and $\mathrm{pt}T_0(\ell)$ a coarse moduli space for such objects with extra level $\ell$ ($h\mathcal{Y}_0$), and two morphisms $d_{00}(\ell), d_{10}(\ell)$ to $\mathcal{X}_0$ over $\operatorname{Spec}\mathcal{O}_0$ ($hd_0f$, $hd_1f$) realising on points the forgetting of the extra level ($hd_0$) and the passage to a level-$\ell$ isogenous object ($hd_1$). Endomorphisms $ar$, $\overline{ar}$ of $\mathcal{X}_0$ over $\operatorname{Spec}\mathcal{O}_0$ ($harf$, $harbarf$) realising on points the Atkin–Lehner quotient at $q'$ ($har$) and at $q$ ($harbar$).
--
--   **The Čerednik–Drinfeld uniformisation.** Maps $\Theta$ and $\Theta T(\ell)$ sending, for every $\mathcal{O}_0$-algebra $B$ in which $\pi$ is nilpotent, a pair consisting of an $\mathcal{O}_0$-algebra map $Onr \to B$ and a Deligne datum over $B$ to a $B$-point of $f_0$, respectively of $g_0(\ell)$, over $\operatorname{Spec}\mathcal{O}_0$. The hypothesis $hCD$ (twelve clauses, summarised here) asserts: naturality of $\Theta$ and of each $\Theta T(\ell)$ in $B$; invariance of $\Theta$ under the twisted action of elements of `awayUnits R₂ v₁`, and of $\Theta T(\ell)$ under the twisted action of the intersection of that group with its conjugate by $s_1$; over an algebraically closed field and for a fixed map $Onr \to k$, surjectivity of $\Theta$ and of each $\Theta T(\ell)$ in the Deligne-datum variable together with the identification of their fibres with the orbits of those groups; the universal property of $\Theta$ and of each $\Theta T(\ell)$ among such naturally transforming, invariant families; the compatibility of $\Theta T(\ell)$ with $d_{00}(\ell)$ and, via the twisted action of $s_1(\ell)$, with $d_{10}(\ell)$; and finally that $ar$ corresponds to the Frobenius twist by $Fr$ on the first coordinate and $\overline{ar}$ to the twisted action of $\bar w_1(\mathrm{none})$.
--
--   **Comparison over the completion and the pinning.** The base changes $\mathcal{X}_C$ and, for each $\ell$, of $g_0(\ell)$ to $C$ are assumed integral ($hXCint$, $hYCint$). An isomorphism $u$ between the fibre product of $\pi_X$ with $\operatorname{Spec}$ of $C \to$ (algebraic closure of $\mathbb{Q}$) $\to \operatorname{Spec}\mathbb{Z}[1/D]$ and $\mathcal{X}_C$, compatible with the projections to $\operatorname{Spec} C$ ($hu$) and with the moduli points $\mathrm{pt}$ and $\mathrm{pt}_0$ ($hupt$). Finally a ring map $j$ from $\bar F$ to the function field of $\mathcal{X}_C$, pinned by $hpin$: for every $x \in \bar F$, every open $U$ of $\mathfrak{M}.C$ containing its generic point, every section $sec$ over $U$ whose germ at the generic point is $\mathfrak{M}.\mathrm{ffEquiv}\,x$, the germ at the generic point of $\mathcal{X}_C$ of the pullback of $sec$ along the composite of $u^{-1}$, the canonical lift into the fibre product of $\pi_X$ over the algebraic closure of $\mathbb{Q}$, and the inverse of $e_{\mathfrak{M}}$, equals $j\,x$.
--
--   **Conclusion.** Two assertions hold.
--
--   First, for every endomorphism $a_{XC}$ of $\mathcal{X}_C$ such that $a_{XC}$ followed by the first projection equals the first projection followed by $ar$, and $a_{XC}$ followed by the second projection equals the second projection, and for every $x \in \bar F$, every open $U$ of $\mathcal{X}_C$ containing the generic point of $\mathcal{X}_C$ (which also lies in $a_{XC}^{-1}U$) and every section $sec$ over $U$: if the germ of $sec$ at the generic point is $j\,x$, then the germ at the generic point of the pullback $(a_{XC}.\mathrm{app}\,U)\,sec$ over $a_{XC}^{-1}U$ is $j\,(W_1 \cdot x)$.
--
--   Second, with $\overline{ar}$ in place of $ar$ and under the same two compatibilities with the projections, the corresponding germ at the generic point of $(a_{XC}.\mathrm{app}\,U)\,sec$ is $j\,(W_0 \cdot x)$.
--
--   This is the step which identifies, on function fields, the two Atkin–Lehner endomorphisms of the Čerednik–Drinfeld integral model after base change to the completion at a place above $q'$ with the prescribed semilinear automorphisms $W_1$ and $W_0$ of the function field $\bar F$ of the Shimura curve model; the identification is read off germs of sections at the generic point, through the pinned embedding $j$. It is used by [`CerednikDrinfeld.exists_ringHom_functionField_of_iso_pullback_completion_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_ringHom_functionField_of_iso_pullback_completion_one_zero_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd.lean

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
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.germ_app_atkinLehner_eq_of_germ_eq_of_iso_pullback_completion_one_zero_of_two_mul_dvd
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
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]
    [hYCint : ∀ ℓ : HeckeTower.AwayPrime q' q, IsIntegral (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]

    (u : (Limits.pullback πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) ≅ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))))
    (hu : u.hom ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A₁.valuation.Completion)) (E : FakeEllipticCurve Λ N S),
        Limits.pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).1 s (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).2 ≫ u.hom =
          Limits.pullback.lift (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).1 s (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).2)

    (j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).functionField)
    (hpin : ∀ (x : Fbar) (U : 𝔐.C.Opens) (hU : (genericPoint (𝔐.C : Scheme.{0})) ∈ U)
        (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ (u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U)
        (sec : 𝔐.C.presheaf.obj (Opposite.op U)),
        (𝔐.C.presheaf.germ U (genericPoint (𝔐.C : Scheme.{0})) hU).hom sec = 𝔐.ffEquiv x →
        ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ ((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom (((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐).app U).hom sec) = j x)
    :

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ ar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 1 • x)) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ arbar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 0 • x)) := by sorry
