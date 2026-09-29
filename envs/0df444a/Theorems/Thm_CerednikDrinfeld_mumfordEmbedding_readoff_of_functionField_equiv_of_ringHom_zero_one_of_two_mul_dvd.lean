-- Prove2me | Theorems.Thm_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
-- name    : CerednikDrinfeld.mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/4d0f8763-c31d-5c8a-a5cf-b4589c4f3934
-- title:
--   Reading off the Mumford embedding from Čerednik–Drinfeld data
-- statement:
--   Numerical data. A squarefree nonzero level $N$, two primes $q,q'$ with $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q,q'\ge 5$, and a nonzero natural number $D$ divisible by $2Nqq'$.
--
--   The place above $q$. A valuation subring $A_2$ of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\,\mathbb Q$ with `hA₂ : A₂.LiesOverPrime q`, i.e. the image of $q$ lies in the nonunits of $A_2$; the instance `hiso₂` records that every element of the decomposition subgroup of $A_2$ over $\mathbb Q$ preserves $A_2$'s valuation. Throughout, $\widehat K:=A_2.\mathrm{valuation.Completion}$ and $K_0:=\mathrm{ratClosure}\,A_2$, the topological closure of $\bot$ inside $\widehat K$. Further, a height-one prime $v_2$ of $\mathcal O_{\mathbb Q}$ containing $q$.
--
--   The definite side (group indices). Rationals $a_1,b_1$ with `hdef₁`: $a_1<0$, $b_1<0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a_1,b_1]\otimes_{\mathbb Q}\mathbb Q_v$ is a division ring exactly when $q'\in v$. A maximal order $\Lambda_1$ (an order, maximal among orders) and an Eichler order $R_1$ of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first), with $R_1\le\Lambda_1$; a finite-idele unit $n_1$ in $\mathrm{primeHeckeSet}\,R_1\,q$ (the four box conditions of that definition); `hS₁`, that $\mathrm{meetOrder}\,R_1\,n_1=R_1\cap n_1R_1n_1^{-1}$ is Eichler of level $Nq$; `hnorm₁`, that conjugation by $n_1$ fixes $\mathrm{meetOrder}\,R_1\,n_1$; `hsq₁`, that the shift by $n_1$ on the class set of the finite-idele stabiliser of $\mathrm{meetOrder}\,R_1\,n_1$ is an involution; finiteness of the two class sets in play; and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁`, i.e. the edge Hecke matrices commute with one another, the vertex Hecke matrices commute with one another, the two degeneracy maps intertwine edge and vertex Hecke operators at primes other than $q$, and the joint kernel of the degeneracy maps is stable under the edge Hecke operators.
--
--   The indefinite side (moduli). Rationals $a,b$ with `hB : IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division ring exactly for the primes $v$ containing $q$ or $q'$; and a maximal order $\Lambda$.
--
--   The generic fibre. A field $\bar F$ over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ (principal divisors of degree $0$ exist, residue fields of places are finite-dimensional, $\Omega$ is free of rank one) and essentially of finite type. A scheme $X$ with a morphism $\pi_X$ to $\mathrm{Spec}$ of $\mathrm{Localization.Away}\,(D:\mathbb Z)$, a point $\bar s$ of that base with values in $\overline{\mathbb Q}$, and an assignment $\mathrm{pt}$ sending a fake elliptic curve for $(\Lambda,N)$ over a commutative ring $S$ and a base point $s$ to an $S$-point of $\pi_X$; the hypotheses `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective` are the four non-universal clauses of `IsCoarseModuli` for this datum: invariance under isomorphism, compatibility with base change along a ring map, and bijectivity of $\mathrm{pt}$ modulo isomorphism on geometric points. A curve model $\mathfrak M$ of $\bar F$ over $\overline{\mathbb Q}$, an isomorphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to the pullback of $\pi_X$ along $\bar s$ with $e_{\mathfrak M}$ followed by the second projection equal to $\mathfrak M.\mathrm{toBase}$, a homomorphism $\mathrm{gal}$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the semilinear automorphisms of $\bar F$ over $\overline{\mathbb Q}$, tower data $\mathbb T$ of type `HeckeTower.TowerData q q' Fbar` with Galois actions $\mathrm{galT}$ on each $\mathbb T.F\ell$, two semilinear automorphisms $W$ of $\bar F$ and $WT$ at each level, and a witness $\mathrm{tw} : \mathrm{ModuliTowerWitnessD}\ \Lambda\,N\,q\,q'\,D\,\bar F\,X\,\pi_X\,\bar s\,\mathrm{pt}\,\mathfrak M\,e_{\mathfrak M}\,\mathrm{gal}\,\mathbb T\,\mathrm{galT}\,W\,WT$, which supplies fake elliptic curves representing the places of $\bar F$ and of each $\mathbb T.F\ell$, matches their coarse moduli points with the points of the curve model, and records the semilinearity of $\mathrm{gal},\mathrm{galT}$ over the given Galois automorphism, the triviality of $W,WT$ on $\overline{\mathbb Q}$ and the degeneracy and Atkin–Lehner relations in the tower.
--
--   Matrix realisation. An injective $\mathbb Q$-algebra map $\iota_2:\mathbb H[\mathbb Q,a_1,b_1]\to M_2(K_0)$, the induced projective representation $\rho_2$ of the units into $\mathrm{PGL}_2(K_0)$ with `hρ₂` stating that $\rho_2$ is the class of $\iota_2$, a pseudo-uniformizer $\varpi_2$ of $K_0$ in $\widehat K$ whose image in $\widehat K$ is $q$ (`hϖ₂`), and the assumption that the holomorphic ring $\mathrm{HolRingOf}\,\varpi_2\,\rho_2$ (functions on the upper half plane holomorphic on each affinoid, carrying the action of the unit group through $\rho_2$) is a domain.
--
--   Hecke elements and level groups. Elements $s_2(\ell)\in\mathbb H[\mathbb Q,a_1,b_1]^\times$ and finite ideles $sf_2(\ell)$ for each prime $\ell$ different from $q,q'$, with `hs₂`: away from $q$ the local component of $sf_2(\ell)$ is $s_2(\ell)\otimes 1$, at $q$ it is $1$, the product of the diagonal of $\ell$ with $sf_2(\ell)^{-1}$ lies in $\mathrm{levelHeckeUSet}\,\Lambda_1(\mathrm{meetOrder}\,R_1\,n_1)\,\ell$ when $\ell\mid N$ and in $\mathrm{primeHeckeSet}(\mathrm{meetOrder}\,R_1\,n_1)\,\ell$ otherwise, and the reduced norm of $s_2(\ell)$ is $\ell$. Subgroups $\Gamma_2$ indexed by $\mathrm{Option}$ of the primes away from $q,q'$, with `hΓ₂0`: $\Gamma_2(\mathrm{none})$ consists of the units lying, at every prime $w\ne v_2$, in the group generated by the local box units of $R_1$, and whose reduced norm has even $q$-adic valuation; and `hΓ₂ℓ`: $\Gamma_2(\mathrm{some}\,\ell)=\Gamma_2(\mathrm{none})\cap s_2(\ell)\Gamma_2(\mathrm{none})s_2(\ell)^{-1}$. Atkin–Lehner elements $w_2,\bar w_2$ indexed likewise, with `hw₂` (at each index: away-integrality with respect to $R_1$, respectively $\mathrm{meetOrder}\,R_1\,sf_2(\ell)$, at $v_2$, and reduced norm $q$) and `hwbar₂` (at each index: reduced norm $q'$, away-unit integrality at the primes different from $v_2$ not containing $q'$, and conjugation-invariance of the local boxes of $R_1$, respectively $\mathrm{meetOrder}\,R_1\,sf_2(\ell)$, and of $\Lambda_1$).
--
--   Galois data at $q$. A homomorphism $dIso_2$ from the decomposition subgroup of $A_2$ over $\mathbb Q$ to the isometric automorphisms of $\widehat K$ over $K_0$, with `hdIso₂` stating that $dIso_2(\tau)$ acts as $\tau$; a character $\chi$ of that subgroup with values in $\mathrm{Multiplicative}(\mathbb Z/2)$, trivial on inertia (`hχ₁`), nontrivial at any Frobenius at $q$ (`hχ₂`), and such that $\chi\tau=1$ holds exactly when $\tau$ fixes every element $x$ of the residue field of $A_2$ with $x^{q^2}=x$ (`hχ₃`).
--
--   The unramified coefficient rings. A char-zero discrete valuation ring $\mathcal O_0$ with irreducible $\pi$, $\pi$-adically complete, residue cardinality $q$, with $(q)=(\pi)$, whose fraction field is $K_0$; a char-zero domain $\mathcal O^{nr}$ over $\mathcal O_0$ with an $\mathcal O_0$-automorphism $\mathrm{Fr}$, $\pi$-adically complete, with $(\pi)$ maximal, integral over $\mathcal O_0$ modulo $\pi$ (`hOa`), such that every monic polynomial of positive degree has a root modulo $\pi$ (`hOcl`), and with $\mathrm{Fr}(x)\equiv x^q \pmod\pi$ (`hFr`); a homomorphism $\mathrm{vdet}$ from $\mathrm{GL}_2(K_0)$ to $\mathrm{Multiplicative}\,\mathbb Z$ characterised by `hvdet` as the $\pi$-valuation of the determinant up to units of $\mathcal O_0$; a ring map $\psi_0:\mathcal O^{nr}\to\widehat K$ with values of valuation $\le 1$ (`hψ₀`) and compatible with $\mathcal O_0\to K_0\to\widehat K$ (`hψ₀𝒪`); the identifications `hπϖ` ($\pi$ maps to $\varpi_2.\varpi$), `hN₀` ($N$ invertible in $\mathcal O_0$), `h𝒪₀` (the image of $\mathcal O_0$ in $K_0$ is the set of elements of valuation $\le 1$) and `hrk` (an archimedean comparison of valuations in $\widehat K$).
--
--   Integral models and correspondences over $\mathcal O_0$. A scheme $\mathcal X_0$ with $f_0$ to $\mathrm{Spec}\,\mathcal O_0$ and a moduli assignment $\mathrm{pt}_0$ making it a coarse moduli space for $(\Lambda,N)$ in the full sense of `IsCoarseModuli` (`h𝒳₀`), with $\mathcal X_0$ integral and $f_0$ flat, separated, locally of finite type and quasi-compact; schemes $\mathcal Y_0(\ell)$ with $g_0(\ell)$ and $\mathrm{ptT}_0(\ell)$ coarse moduli for the level-$\ell$ problem (`h𝒴₀`); degeneracy morphisms $d_{00}(\ell),d_{10}(\ell):\mathcal Y_0(\ell)\to\mathcal X_0$ over the base (`hd₀f`, `hd₁f`) with `hd₀` (composition with $d_{00}$ forgets the extra level) and `hd₁` (composition with $d_{10}$ computes the target of a level-$\ell$ isogeny); endomorphisms $\mathrm{ar},\overline{\mathrm{ar}}$ of $\mathcal X_0$ over the base (`harf`, `harbarf`) realising the Atkin–Lehner quotients at $q$ and at $q'$ on moduli points (`har`, `harbar`).
--
--   The Čerednik–Drinfeld uniformisation. Maps $\Theta$ and $\Theta_T(\ell)$ from the functor $B\mapsto (\mathcal O^{nr}\to_{\mathcal O_0}B)\times\mathrm{DeligneDatum}$ on $\mathcal O_0$-algebras with $\pi$ nilpotent to the nilpotent points of $f_0$, respectively of $g_0(\ell)$, and the hypothesis `hCD`, a conjunction of: naturality of $\Theta$ and of each $\Theta_T(\ell)$; invariance of $\Theta$ under the twisted action (in the sense of `OmegaNr.IsTwistedAct`: Frobenius twist of the first coordinate by $-\mathrm{vdet}$ and pullback of the Deligne datum by the inverse matrix) of the units integral away from $v_2$ for $R_1$, and of $\Theta_T(\ell)$ under that of the intersection of this group with its $s_2(\ell)$-conjugate; surjectivity of $\Theta(\psi,\cdot)$ and identification of its fibres with the orbits of these groups over algebraically closed fields, for $\Theta$ and for each $\Theta_T(\ell)$; the universal property of $\Theta$ and of each $\Theta_T(\ell)$ as the quotient of the formal functor by those groups; compatibility of $\Theta_T(\ell)$ with $d_{00}(\ell)$ and, through the twisted action of $s_2(\ell)$, with $d_{10}(\ell)$; and compatibility of $\Theta$ with $\mathrm{ar}$ (Frobenius twist by $1$ in the first coordinate) and with $\overline{\mathrm{ar}}$ (the twisted action of $\bar w_2(\mathrm{none})$).
--
--   The generic-fibre read-off data. Integrality of the base changes of $f_0$ and of each $g_0(\ell)$ along $\mathcal O_0\to K_0\to\widehat K$; the hypothesis `hGF`, which provides an isomorphism $e$ from the function field of the base change of $f_0$ to $\widehat K$ onto the $\Gamma_2(\mathrm{none})$-invariant subfield of $\mathrm{FractionRing}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$, compatible with constants from $\widehat K$, transporting any endomorphism of the base change lying over an endomorphism of $\mathcal X_0$ that is $\Theta$-intertwined with the twisted action of a unit $g$ with $\mathrm{vdet}=1$ into the action of $g^{-1}$ on germs at the generic point, transporting any endomorphism lying over an endomorphism $\Theta$-intertwined with the Frobenius twist by $1$ into the action of $w^{-1}$ for any away-integral $w$ with $\mathrm{vdet}(w)=\mathrm{ofAdd}\,1$, transporting a semilinear endomorphism over an isometric automorphism $s$ satisfying $s\circ\psi_0=\psi_0\circ\mathrm{Fr}^n$ on $\mathrm{Fr}$-involutive elements into $w^n$ composed with the semilinear map induced by $s$, and giving at each level $\ell$ an analogous isomorphism $e_Y$ onto the $\Gamma_2(\mathrm{some}\,\ell)$-invariant field, compatible with constants and with the degeneracy morphisms through the action of $g^{-1}$.
--
--   The comparison map. A ring homomorphism $j$ from $\bar F$ to the function field of the base change of $f_0$, together with `hj`: $j$ is compatible with constants from $\overline{\mathbb Q}$; the subfield generated by the constants and the image of $j$ is everything; any finite subset of $\bar F$ linearly independent over $\overline{\mathbb Q}$ has $j$-image linearly independent over $\widehat K$; any lift of $\mathrm{ar}$ (respectively $\overline{\mathrm{ar}}$) to the base change sends a germ equal to $j(x)$ to $j(W_0\cdot x)$ (respectively $j(W_1\cdot x)$); any lift over the action of $\tau$ in the decomposition subgroup sends $j(x)$ to $j(\mathrm{gal}(\tau)\cdot x)$; and for each $\ell$ there is $j_\ell$ on $\mathbb T.F\ell$ with the two degeneracy lifts sending $j(x)$ to $j_\ell(\mathbb T.\varphi(\ell,k)x)$.
--
--   Conclusion. There exists a ring homomorphism $\iota_0:\bar F\to\mathrm{FractionRing}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$ such that:
--
--   1.
--
--   for every $z\in\overline{\mathbb Q}$, $\iota_0$ of the image of $z$ in $\bar F$ is the image of $z$ under $\widehat K\to\mathrm{FractionRing}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$;
--
--   2.
--
--   the subfield generated by the image of $\widehat K$ together with the image of $\iota_0$ equals the field of $\Gamma_2(\mathrm{none})$-invariants $\mathrm{invariantFieldOf}\,\widehat K\,(\mathbb H[\mathbb Q,a_1,b_1])^\times(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)\,(\Gamma_2(\mathrm{none}))$;
--
--   3.
--
--   for every finite subset $t$ of $\bar F$ whose elements are linearly independent over $\overline{\mathbb Q}$, the family $\iota_0$ of those elements is linearly independent over $\widehat K$;
--
--   4.
--
--   for every $\tau$ in the decomposition subgroup of $A_2$ over $\mathbb Q$ and every $x\in\bar F$, $\iota_0(\mathrm{gal}(\tau)\cdot x)$ equals $\big(1$ if $\chi\tau=1$, and $w_2(\mathrm{none})$ otherwise$\big)$ acting on the image of $\iota_0(x)$ under the semilinear automorphism of the fraction field induced by $dIso_2(\tau)$ via $\mathrm{toAmbientOf}\,\varpi_2\,\rho_2$;
--
--   5.
--
--   $\iota_0(W_0\cdot x)=w_2(\mathrm{none})\cdot\iota_0(x)$ for all $x\in\bar F$;
--
--   6.
--
--   $\iota_0(W_1\cdot x)=\bar w_2(\mathrm{none})\cdot\iota_0(x)$ for all $x\in\bar F$;
--
--   7.
--
--   for every prime $\ell$ different from $q$ and $q'$ there is a ring homomorphism $\iota_\ell$ from $\mathbb T.F\ell$ to $\mathrm{FractionRing}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$ with $\iota_\ell(\mathbb T.\varphi(\ell,0)x)=\iota_0(x)$ and $\iota_\ell(\mathbb T.\varphi(\ell,1)x)=s_2(\ell)\cdot\iota_0(x)$ for all $x\in\bar F$.
--
--   This is the read-off step of the Čerednik–Drinfeld $p$-adic uniformisation of the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: composing the comparison map $j$ on the generic fibre with the function-field identification $e$ produces an explicit embedding of the field $\bar F$ into the fraction field of the holomorphic ring of the upper half plane, with the Galois action at $q$, the two Atkin–Lehner involutions and the Hecke tower all expressed by quaternion units. It is used by [`CerednikDrinfeld.mumfordEmbedding_assembly_of_functionField_equiv_zero_one_of_two_mul_dvd`](thm.html#CerednikDrinfeld.mumfordEmbedding_assembly_of_functionField_equiv_zero_one_of_two_mul_dvd), which assembles these embeddings into the comparison of the curve with a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_zero_one_of_two_mul_dvd
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
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]
    [hYCint : ∀ ℓ : HeckeTower.AwayPrime q q', IsIntegral (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]
    (hGF :
    ∃ _ : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
    ∃ e : ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)),

      (∀ c : A₂.valuation.Completion, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) c) =
        algebraMap A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)) c) ∧

      (∀ (aX : 𝒳₀ ⟶ 𝒳₀) (haX : aX ≫ f₀ = f₀) (g : (ℍ[ℚ, a₁, b₁])ˣ), vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) = 1 →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
            CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) x x' → (Scheme.nilpPoints.mapHom f₀ f₀ aX haX).app B (Θ B hB x) = Θ B hB x') →
        ∀ (aXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ aX → aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ aXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((aXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ (bX : 𝒳₀ ⟶ 𝒳₀) (hbX : bX ≫ f₀ = f₀),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
            (Scheme.nilpPoints.mapHom f₀ f₀ bX hbX).app B (Θ B hB x) = Θ B hB (CerednikDrinfeld.FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) →
        ∀ (bXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          bXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ bX → bXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ (w : (ℍ[ℚ, a₁, b₁])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂) → vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ bXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (bXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((bXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            w⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ (s : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion) (n : ℤ),
        (∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪₀] Onr) y)) →
        ∀ (tC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
          tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
          tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : A₂.valuation.Completion →+* A₂.valuation.Completion)) →
        ∀ (w : (ℍ[ℚ, a₁, b₁])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂) → vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec)) :
              ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ s)
              ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom sec) :
                ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ i : (HeckeTower.AwayPrime q q'), ∃ _ : IsIntegral (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
        ∃ eY : ↑(Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i)),
          (∀ c : A₂.valuation.Completion, eY (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) c) =
            algebraMap A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i)) c) ∧
          (∀ (h : 𝒴₀ i ⟶ 𝒳₀) (hhf : h ≫ f₀ = g₀ i) (g : (ℍ[ℚ, a₁, b₁])ˣ), vdet ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) = 1 →
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
                (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₂) π)).obj B),
                CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))) g) x x' →
                  (Scheme.nilpPoints.mapHom (g₀ i) f₀ h hhf).app B (ΘT i B hB x) = Θ B hB x') →
            ∀ (hC : Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))),
              hC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ h →
              hC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
            ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ U)
              (hU' : genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0}) ∈ hC ⁻¹ᵁ U)
              (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
              ((eY (((Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (hC ⁻¹ᵁ U) (genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU').hom
                  ((hC.app U).hom sec)) : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) ((fun ℓ => Γ₂ (some ℓ)) i))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
                g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) : Scheme.{0})) hU).hom sec) :
                  ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)))))

    (j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField)
    (hj :

      (∀ z : AlgebraicClosure ℚ, j (algebraMap (AlgebraicClosure ℚ) Fbar z) = (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧

      (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j) = ⊤) ∧

      (∀ (t : Finset Fbar), LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
        ∀ c : t → A₂.valuation.Completion, (∑ x : t, (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) (c x) * j (x : Fbar)) = 0 → ∀ x : t, c x = 0) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ ar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 0 • x)) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ arbar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 1 • x)) ∧

      (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (tC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))),
        tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
        tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ Spec.map (CommRingCat.ofHom ((dIso₂ τ).toRingEquiv : A₂.valuation.Completion →+* A₂.valuation.Completion)) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec) = j ((gal.comp (A₂.decompositionSubgroup ℚ).subtype) τ • x)) ∧

      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ jℓ : 𝕋.F ℓ →+* ↑(Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField,
        ∀ (k : Fin 2) (dC : (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))),
          dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.fst (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) ≫ (if k = 0 then d₀₀ ℓ else d₁₀ ℓ) →
          dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) →
          ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ dC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ (dC ⁻¹ᵁ U) (genericPoint ((Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom ((dC.app U).hom sec) = jℓ (𝕋.φ (ℓ, k) x)))
    :
    ∃ ι₀ : Fbar →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂),
      (∀ z : AlgebraicClosure ℚ, ι₀ (algebraMap (AlgebraicClosure ℚ) Fbar z) =
          algebraMap A₂.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧
      (Subfield.closure (Set.range (algebraMap A₂.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∪ Set.range ι₀) =
          Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ none)) ∧
      (∀ t : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
          LinearIndependent A₂.valuation.Completion (fun x : t => ι₀ (x : Fbar))) ∧
      (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : Fbar),
          ι₀ ((gal.comp (A₂.decompositionSubgroup ℚ).subtype) τ • x) =
            (if χ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ none) •
              Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (ι₀ x)) ∧
      (∀ x : Fbar, ι₀ (W 0 • x) = w₂ none • ι₀ x) ∧
      (∀ x : Fbar, ι₀ (W 1 • x) = wbar₂ none • ι₀ x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ ιℓ : 𝕋.F ℓ →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂),
      (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 0) x) = ι₀ x) ∧ (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 1) x) = (s₂ ℓ) • ι₀ x)) := by sorry
