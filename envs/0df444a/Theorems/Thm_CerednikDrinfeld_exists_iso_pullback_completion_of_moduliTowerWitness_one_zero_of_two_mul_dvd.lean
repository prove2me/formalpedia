-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_iso_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd
-- name    : CerednikDrinfeld.exists_iso_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/f9eb7eb3-eed4-50b3-b5e2-71bbca4d5f94
-- title:
--   Comparison of the two coarse models over the q'-adic completion
-- statement:
--   Throughout, $\bar{\mathbb Q}$ is `AlgebraicClosure ℚ`, $A_1$ is a valuation subring of $\bar{\mathbb Q}$, $C$ denotes the completion `A₁.valuation.Completion` of $\bar{\mathbb Q}$ for the valuation attached to $A_1$, and $K_0$ denotes [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13), the topological closure of the prime subfield inside $C$.
--
--   **Numerical data.** A nonzero squarefree integer $N$; primes $q,q'$ with $q'\ne q$, $5\le q$, $5\le q'$, and $q\nmid N$, $q'\nmid N$; a nonzero integer $D$ with $2Nqq'\mid D$.
--
--   **The place above $q'$.** A valuation subring $A_1\subseteq\bar{\mathbb Q}$ with $q'$ a non-unit of $A_1$ (`hA₁`), the assumption that every element of the decomposition subgroup of $A_1$ over $\mathbb Q$ preserves `A₁.valuation` (`hiso₁`), and a height-one prime $v_1$ of $\mathcal O_{\mathbb Q}$ containing $q'$ (`hv₁`).
--
--   **Definite quaternion data.** Rationals $a_2,b_2$ with `hdef₂`: $a_2<0$, $b_2<0$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q\in v$. Two $\mathbb Z$-submodules $\Lambda_2,R_2$ of $\mathbb H[\mathbb Q,a_2,b_2]$ with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$), and $R_2\le\Lambda_2$; a finite-idelic unit $n_2$ lying in `primeHeckeSet R₂ q'` (the box conditions: $n_2$ lies in the finite adelic box of $R_2$, $q'\,n_2^{-1}$ lies in it, while $n_2^{-1}$ and $q'^{-1}n_2$ do not). Furthermore `hS₂`: `meetOrder R₂ n₂` $=R_2\cap n_2R_2n_2^{-1}$ is an Eichler order of level $Nq'$; `hnorm₂`: conjugation by $n_2$ fixes this order; `hsq₂`: the right shift by $n_2$ on the class set of [`Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)`](def/Submodule_FiniteAdeleBox.html#L26) is an involution; finiteness (and decidability) of the two class sets involved; and `hlaws₂`, the four Hecke laws `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`: the edge operators pairwise commute, the vertex operators pairwise commute, for every prime $\ell\ne q'$ the two degeneracy pushforwards intertwine the edge and vertex operators, and the joint kernel of the two degeneracy pushforwards is stable under every edge operator.
--
--   **Indefinite quaternion data.** Rationals $a,b$ with `hB`: $0<a$ or $0<b$, and $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly at the primes $v$ above $q$ and $q'$; a maximal order $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$.
--
--   **Generic model and tower.** A field $Fbar$ over $\bar{\mathbb Q}$ which is a curve over $\bar{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors of degree zero for all nonzero elements, residue fields of all places finite over $\bar{\mathbb Q}$, and $\Omega_{Fbar/\bar{\mathbb Q}}$ free of rank one) and essentially of finite type over $\bar{\mathbb Q}$. A scheme $X$ with $\pi_X:X\to\operatorname{Spec}\mathbb Z[1/D]$ (here $\mathbb Z[1/D]$ is `Localization.Away ((D : ℕ) : ℤ)`), a point $\overline s:\operatorname{Spec}\bar{\mathbb Q}\to\operatorname{Spec}\mathbb Z[1/D]$, and an assignment `pt` sending a fake elliptic curve of level $N$ for $\Lambda$ over a ring $S$, together with a structure morphism $s$, to a point of $X$ over $s$. The hypotheses `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective` are the four moduli clauses of `IsCoarseModuli` for $(X,\pi_X,\mathrm{pt})$ — invariance under isomorphism of fake elliptic curves, compatibility with base change along ring homomorphisms, and surjectivity and injectivity up to isomorphism on points valued in algebraically closed fields — the universal property not being assumed here. A curve model $\mathfrak M$ of $Fbar$ over $\bar{\mathbb Q}$ together with an isomorphism $e_{\mathfrak M}:\mathfrak M.C\to X\times_{\operatorname{Spec}\mathbb Z[1/D]}\operatorname{Spec}\bar{\mathbb Q}$ whose composite with the second projection is $\mathfrak M.toBase$. A homomorphism $gal$ from $\operatorname{Aut}_{\mathbb Q}(\bar{\mathbb Q})$ to the semilinear automorphisms of $Fbar$ over $\bar{\mathbb Q}$; tower data $\mathbb T$ of type `HeckeTower.TowerData q q' Fbar` with semilinear Galois actions $gal_T$ on each tower field and involutions $W$, $W_T$; and a witness $tw$ of type `ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT`, whose fields (summarised here) parametrise the places of $Fbar$ and of the tower fields by fake elliptic curves over $\bar{\mathbb Q}$, with and without extra level structure, compatibly with `pt` and with the curve model, normalise the base automorphisms of $gal$, $gal_T$, $W$, $W_T$, and record the compatibilities of the degeneracy maps of the tower with level structures.
--
--   **The $q'$-adic uniformisation data.** An injective $\mathbb Q$-algebra map $\iota_1:\mathbb H[\mathbb Q,a_2,b_2]\to M_2(K_0)$ and the induced projective representation $\rho_1$ on units, with `hρ₁` identifying $\rho_1$ with the projectivisation of $\iota_1$. A pseudo-uniformiser $\varpi_1$ of $K_0$ in $C$ (an element of positive valuation less than one satisfying the scaling condition) whose image in $C$ is $q'$ (`hϖ₁`), together with the assumption that `Omega.HolRingOf ϖ₁ ρ₁` is a domain. Families $s_1,sf_1$ indexed by the primes $\ell\notin\{q,q'\}$ with `hs₁`: for each $\ell$, $sf_1(\ell)$ localises to $s_1(\ell)\otimes 1$ at every prime not containing $q'$ and to $1$ at every prime containing $q'$; the product of the diagonal idele of $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise; and $\mathrm{nrd}(s_1(\ell))=\ell$. A family of subgroups $\Gamma_1$ indexed by `HeckeTower.Obj q q'` with `hΓ₁0`: $\Gamma_1(\mathrm{none})$ consists of the units lying in every local box of $R_2$ away from $v_1$ and having even $q'$-adic valuation of reduced norm; and `hΓ₁ℓ`: $\Gamma_1(\mathrm{some}\,\ell)=\Gamma_1(\mathrm{none})\cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$. Elements $w_1,\bar w_1$ with `hw₁` ($w_1(\mathrm{none})$ away-integral for $R_2$ at $v_1$ of reduced norm $q'$, and similarly $w_1(\mathrm{some}\,\ell)$ for `meetOrder R₂ (sf₁ ℓ)`) and `hwbar₁` (reduced norm $q$, away-integrality at the primes not containing $q$, and normalisation of the local boxes of $R_2$, of `meetOrder R₂ (sf₁ ℓ)`, and of $\Lambda_2$ at all primes $\ne v_1$). A homomorphism $dIso_1$ from the decomposition subgroup to the isometric automorphisms of $C$ over $K_0$ realising the Galois action (`hdIso₁`). A quadratic character $\chi$ of the decomposition subgroup, trivial on inertia (`hχ₁`), nontrivial on every Frobenius at $q'$ (`hχ₂`), and with kernel the stabiliser of the elements of the residue field of $A_1$ satisfying $x^{q'^2}=x$ (`hχ₃`).
--
--   **Coefficient rings.** A characteristic-zero domain $\mathcal O_0$ which is a discrete valuation ring, with irreducible $\pi$, $\pi$-adically complete, residue cardinality $q'$, and $(q')=(\pi)$, whose fraction field is $K_0$; the image of $\mathcal O_0$ in $K_0$ is exactly the set of elements of valuation at most one (`h𝒪₀`), $\pi$ maps to $\varpi_1$ (`hπϖ`), and $N$ is a unit of $\mathcal O_0$ (`hN₀`). A characteristic-zero $\mathcal O_0$-domain $Onr$ with an $\mathcal O_0$-algebra automorphism $Fr$, complete for the $\pi$-adic topology, with $(\pi)$ maximal, every element integral over $\mathcal O_0$ modulo $\pi$, every monic polynomial of positive degree having a root modulo $\pi$, and $Fr(x)\equiv x^{q'}\pmod\pi$; thus the residue ring of $Onr$ is an algebraic closure of that of $\mathcal O_0$ and $Fr$ is a Frobenius lift. A homomorphism $vdet:GL_2(K_0)\to\mathbb Z$ (written multiplicatively) characterised by `hvdet`: $vdet(g)=n$ precisely when $\det g$ is a unit of $\mathcal O_0$ times $\pi^n$. A ring homomorphism $\psi_0:Onr\to C$ with values of valuation at most one, restricting on $\mathcal O_0$ to the canonical map (`hψ₀`, `hψ₀𝒪`). Finally `hrk`: for $x,y\in C$ with $|x|<1$ and $y\ne0$ there is $n$ with $|x|^n\le|y|$.
--
--   **Integral models over $\mathcal O_0$.** A scheme $\mathcal X_0$ with $f_0:\mathcal X_0\to\operatorname{Spec}\mathcal O_0$ and an assignment $\mathrm{pt}_0$ such that `h𝒳₀` holds: $(\mathcal X_0,f_0,\mathrm{pt}_0)$ is a coarse moduli space for fake elliptic curves of level $N$ for $\Lambda$ in the full sense of `IsCoarseModuli`, including the universal property; moreover $\mathcal X_0$ is integral and $f_0$ is flat, separated, locally of finite type and quasi-compact. For each prime $\ell\notin\{q',q\}$ a scheme $\mathcal Y_0(\ell)$ with $g_0(\ell)$ to $\operatorname{Spec}\mathcal O_0$ and $\mathrm{ptT}_0(\ell)$ making it a coarse moduli space for fake elliptic curves with extra level $\ell$ (`h𝒴₀`), together with two degeneracy morphisms $d_{00}(\ell),d_{10}(\ell):\mathcal Y_0(\ell)\to\mathcal X_0$ over $\operatorname{Spec}\mathcal O_0$ (`hd₀f`, `hd₁f`) which on moduli points forget the extra level (`hd₀`) and pass to the $\ell$-isogeny quotient (`hd₁`). Two endomorphisms $ar,\overline{ar}$ of $\mathcal X_0$ over $\operatorname{Spec}\mathcal O_0$ inducing on moduli points the Atkin–Lehner quotient at $q'$ and at $q$ respectively (`har`, `harbar`).
--
--   **The Čerednik–Drinfeld uniformisation data.** Maps $\Theta$ and $\Theta_T(\ell)$ sending, for each $\mathcal O_0$-algebra $B$ in which $\pi$ is nilpotent, a point of the product functor $(Onr\to_{\mathcal O_0}-)\times\Omega_{K_0,\pi}$ over $B$ to a $B$-point of $f_0$, resp. of $g_0(\ell)$. The hypothesis `hCD` is the conjunction of twelve clauses: naturality of $\Theta$ and of each $\Theta_T(\ell)$ in $B$; invariance of $\Theta$ under the twisted action (`FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet`, composed with $\iota_1$) of the units of $\mathbb H[\mathbb Q,a_2,b_2]$ lying in every local box of $R_2$ away from $v_1$, and invariance of $\Theta_T(\ell)$ under the intersection of that group with its conjugate by $s_1(\ell)$; for each algebraically closed field $k$ with $\pi$ nilpotent and each $\mathcal O_0$-algebra map $\psi:Onr\to k$, surjectivity of $P\mapsto\Theta(\psi,P)$ onto the $k$-points of $f_0$ together with the identification of its fibres with the orbits of that twisted action, and the analogous statement for $\Theta_T(\ell)$ with the intersected group; the universal property of $\Theta$ (every natural, invariant family of maps to the nilpotent points of a morphism $t:T\to\operatorname{Spec}\mathcal O_0$ factors uniquely through $\Theta$ by a natural family) and the same for each $\Theta_T(\ell)$; the compatibility of $d_{00}(\ell)$ with $\Theta_T(\ell)$ and $\Theta$, and of $d_{10}(\ell)$ with the twisted action of $s_1(\ell)$; and the compatibility of $ar$ with the Frobenius twist $Fr^1$ on the $Onr$-coordinate and of $\overline{ar}$ with the twisted action of $\bar w_1(\mathrm{none})$.
--
--   **Conclusion.** Write $c:\bar{\mathbb Q}\to C$ for the canonical map into the completion (`UniformSpace.Completion.coeRingHom` precomposed with the inverse of `WithVal.equiv A₁.valuation`) and $j:\mathcal O_0\to K_0\to C$ for the composite structure map. Then there exists an isomorphism of schemes
--   $$u:\;X\times_{\operatorname{Spec}\mathbb Z[1/D]}\operatorname{Spec}C\;\xrightarrow{\ \sim\ }\;\mathcal X_0\times_{\operatorname{Spec}\mathcal O_0}\operatorname{Spec}C,$$
--   the left-hand fibre product being taken along $\operatorname{Spec}(c)$ followed by $\overline s$ and the right-hand one along $\operatorname{Spec}(j)$, such that:
--
--   (i) $u.\mathrm{hom}$ followed by the second projection of the second pullback equals the second projection of the first pullback; that is, $u$ is an isomorphism over $\operatorname{Spec}C$;
--
--   (ii) for every commutative ring $S$, every morphism $s:\operatorname{Spec}S\to\operatorname{Spec}C$ and every fake elliptic curve $E$ of level $N$ for $\Lambda$ over $S$, the morphism into the first pullback determined by the moduli point $\mathrm{pt}\,S\,(s\circ\operatorname{Spec}(c)\circ\overline s)\,E$ and by $s$, followed by $u.\mathrm{hom}$, equals the morphism into the second pullback determined by the moduli point $\mathrm{pt}_0\,S\,(s\circ\operatorname{Spec}(j))\,E$ and by $s$.
--
--   This is the comparison step of the Čerednik–Drinfeld package: it identifies the base change to the $q'$-adic completion $C$ of $\bar{\mathbb Q}$ of the Shimura-curve model $X$ over $\mathbb Z[1/D]$ with the base change of the integral coarse moduli scheme $\mathcal X_0$ over $\mathcal O_0$, by an isomorphism over $\operatorname{Spec}C$ matching the two moduli-point assignments. It is used by [`CerednikDrinfeld.exists_ringHom_functionField_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_ringHom_functionField_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd), which transports function-field data across this identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_iso_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.exists_iso_pullback_completion_of_moduliTowerWitness_one_zero_of_two_mul_dvd
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
    ∃ u : (Limits.pullback πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) ≅ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
      u.hom ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A₁.valuation.Completion)) (E : FakeEllipticCurve Λ N S),
        Limits.pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).1 s (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).2 ≫ u.hom =
          Limits.pullback.lift (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).1 s (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).2 := by sorry
