-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_zero_one_of_two_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_zero_one_of_two_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/4f96af1b-d758-5ce9-8cdd-c83afa1a36cb
-- title:
--   Descent intertwining base at q from a rigid oriented moduli witness
-- statement:
--   Numerical data. Let $N\ge 1$ be squarefree, let $q,q'$ be primes with $q'\ne q$, neither dividing $N$, and with $5\le q$ and $5\le q'$; let $D\ge 1$ be a natural number divisible by $2Nqq'$.
--
--   The $q$-adic place. Let $A_2$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` with `A₂.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A_2$; the decomposition subgroup of $A_2$ over $\mathbb Q$ is assumed to act isometrically for the valuation of $A_2$ (`A₂.DecompositionIsometric ℚ`). Let $v_2$ be a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q$, and let $dIso_2$ be a homomorphism from the decomposition subgroup to the isometric automorphisms of the completion $A_2^{\mathrm{val}}$ over [`ValuationSubring.ratClosure A₂`](def/ValuationSubring_CompletionRatClosure.html#L13), whose underlying ring equivalence is, by `hdIso₂`, the Galois action ($\,(dIso_2\tau)(x)=\tau\cdot x$).
--
--   The definite side. Let $a_1,b_1\in\mathbb Q$ be such that $\mathbb H[\mathbb Q,a_1,b_1]$ satisfies `IsDefiniteRamifiedExactlyAt q'`: $a_1<0$, $b_1<0$, and for every finite place $v$ of $\mathbb Q$ the algebra $\mathbb H[\mathbb Q,a_1,b_1]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra precisely when $q'\in v$. Let $\Lambda_1$ be a maximal order, $R_1$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$) with $R_1\le\Lambda_1$, and let $n_1$ be a finite-idelic unit lying in `primeHeckeSet R₁ q` (so $n_1$ lies in the finite adelic box of $R_1$, $q\cdot n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $q^{-1}n_1$ do not). The hypotheses on this datum are: `hS₁`, that `meetOrder R₁ n₁` $=R_1\cap n_1R_1n_1^{-1}$ is an Eichler order of level $Nq$; `hnorm₁`, that conjugation by $n_1$ preserves `meetOrder R₁ n₁`; `hsq₁`, that the shift by $n_1$ on the class set of the finite-idelic stabiliser of `meetOrder R₁ n₁` is an involution; finiteness and decidability of the relevant class sets; and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁`, a conjunction of four clauses (commutation of the edge Hecke operators, commutation of the vertex Hecke operators, intertwining of the edge Hecke operators at primes $\ne q$ with the vertex Hecke operators through the two joint degeneracy maps, and stability of the common kernel of the degeneracy maps under the edge Hecke operators).
--
--   The indefinite side and its moduli witness. Let $a,b\in\mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly for the $v$ containing $q$ or $q'$. Let $R$ be an Eichler order of level $N$ in $\mathbb H[\mathbb Q,a,b]$, let $\iota$ be an injective $\mathbb Q$-algebra map $\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb R)$, and let $\Lambda\supseteq R$ be a maximal order. Let $M$ be a `ShimuraCurveModel` for $(R,\iota)$ with Hecke sets $\mathcal S_\ell=$ `levelHeckeUSet Λ R ℓ` for $\ell\mid N$ and `primeHeckeSet R ℓ` otherwise; thus $M$ carries function fields $M.F$ over $\mathbb Q$, $M.\overline F$ over $\overline{\mathbb Q}$ and $M.F_{\mathbb C}$ over $\mathbb C$, each a curve field, together with the comparison map `M.toBar` and the further data of that structure. Let $w$ be a `ModuliWitnessD` for $M$ relative to $\Lambda,N,q,q',D$: an integral scheme $X$ with a smooth proper morphism $\pi_X$ to $\operatorname{Spec}$ of `Localization.Away (D : ℤ)`, a point $\bar s$ over $\overline{\mathbb Q}$ lying over the structure map, an assignment `pt` of $\pi_X$-sections to fake elliptic curves with $\Lambda$-action and level-$N$ structure over arbitrary base rings (invariant under isomorphism, compatible with base change, and bijective on algebraically closed fields), an isomorphism `eF` of $M.F$ with the function field of $X$, and a bijection `pts` between the places of $M.\overline F$ over $\overline{\mathbb Q}$ and the $\bar s$-sections of $\pi_X$. The scheme $w.X$ is assumed integral. The hypothesis `horient : w.IsOriented` states that for every prime $\ell\mid N$ and all places $P,Q$ of $M.\overline F$, $Q$ lies in the support of `M.corrBar ℓ` applied to the divisor $P$ if and only if there are a fake elliptic curve $u$ with extra level structure at $\ell$ and a fake elliptic curve $d$ over $\overline{\mathbb Q}$ with $w.\mathrm{pt}(u_1)=w.\mathrm{pts}(P)$, $w.\mathrm{pt}(d)=w.\mathrm{pts}(Q)$ and $u\to d$ a level isogeny at $\ell$.
--
--   Rigidity of the geometric fibre (`hpts`). It is assumed that there exist a `CurveModel` $\mathfrak M$ of $M.\overline F$ over $\overline{\mathbb Q}$, a morphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to the pullback of $\pi_X$ along $\bar s$ which is an isomorphism, such that: $e_{\mathfrak M}$ followed by the second pullback projection is $\mathfrak M.\mathrm{toBase}$; for every $\overline{\mathbb Q}$-point $x$ of $\mathfrak M.C$ over the base, $w.\mathrm{pts}$ of the place attached to $x$ by `𝔐.pointEquivPlace` is $x$ followed by ($e_{\mathfrak M}$ followed by the first pullback projection); and for every open $U\subseteq X$ and section $t$ over $U$ (with the two nonemptiness instances), the germ in the function field of $\mathfrak M.C$ of the pullback of $t$ along $e_{\mathfrak M}$ followed by the first projection, transported by `𝔐.ffEquiv.symm`, equals `M.toBar` of the germ of $t$ transported by `w.eF.symm`.
--
--   The Hecke tower and the involutions. Let $\varepsilon$ assign to each prime a unit of $\mathbb Z$, with $\varepsilon_\ell=1$ for $\ell\ne q,q'$. Let $\mathbb T$ be a `HeckeTower.TowerData` over $M.\overline F$: for each prime $\ell\notin\{q,q'\}$ a curve field $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$ together with two finite integral $\overline{\mathbb Q}$-algebra maps $\mathbb T.\varphi(\ell,i)\colon M.\overline F\to\mathbb T.F(\ell)$, $i\in\{0,1\}$; the index set `Obj q q'` is $\{\ast\}\sqcup\{\ell\}$ with $\mathbb T.\mathrm{objField}(\ast)=M.\overline F$. The hypothesis `hfg` requires each $\mathbb T.\mathrm{objField}(j)$ to contain an element transcendental over $\overline{\mathbb Q}$ over whose adjoined subfield it is finite-dimensional. Let $galT$ assign to each away prime $\ell$ a homomorphism from $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ to the semilinear automorphisms of $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$, and let $W\colon\mathrm{Fin}\,2\to$ semilinear automorphisms of $M.\overline F$ and $WT(\ell)\colon\mathrm{Fin}\,2\to$ semilinear automorphisms of $\mathbb T.F(\ell)$. The assumptions on these are: `hgalT_base`, the base component of $galT_\ell(\sigma)$ is $\sigma$; `hgalT_φ`, $galT_{\alpha_1}(\sigma)\cdot\mathbb T.\varphi(\alpha)(x)=\mathbb T.\varphi(\alpha)(M.\mathrm{gal}(\sigma)\cdot x)$; `hW_base` and `hWT_base`, the base components of $W_i$ and $WT(\ell)_i$ are the identity on $\overline{\mathbb Q}$; `hW_sq`, `hWT_sq`, each $W_i$ and each $WT(\ell)_i$ is an involution; `hW_comm`, `hWT_comm`, $W_0W_1=W_1W_0$ and likewise on each $\mathbb T.F(\ell)$; `hW_gal`, `hWT_gal`, these involutions commute with the Galois actions; `hWT_φ`, $WT(\alpha_1)_i\cdot\mathbb T.\varphi(\alpha)(x)=\mathbb T.\varphi(\alpha)(W_i\cdot x)$; `hW0_pic` and `hW1_pic`, that on $M.J$ the involution $W_0$ acts as $\varepsilon_q$ times `M.heckePic0 q` and $W_1$ as $\varepsilon_{q'}$ times `M.heckePic0 q'`; `hW0_pl` and `hW1_pl`, that on divisors `M.corrBar q` sends the divisor $P$ to the divisor $W_0\cdot P$ and `M.corrBar q'` sends $P$ to $W_1\cdot P$; `hdeg`, that $\mathrm{finrankAlong}(\mathbb T.\varphi(\alpha))$ equals `HeckeTower.arrowDegree N α`, namely $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise; and `hhecke`, that for every away prime $\ell$ and every divisor of $M.\overline F$, `M.corrBar ℓ` coincides with the divisor correspondence attached to the pair $\mathbb T.\varphi(\ell,0),\mathbb T.\varphi(\ell,1)$.
--
--   The $p$-adic uniformisation data. Let $\iota_2$ be an injective $\mathbb Q$-algebra map $\mathbb H[\mathbb Q,a_1,b_1]\to M_2(\mathrm{ratClosure}\,A_2)$ and $\rho_2$ a homomorphism from $\mathbb H[\mathbb Q,a_1,b_1]^\times$ to $\mathrm{PGL}_2(\mathrm{ratClosure}\,A_2)$ given by `hρ₂` as the projectivisation of $\iota_2$. Let $\varpi_2$ be a pseudo-uniformiser of $\mathrm{ratClosure}\,A_2$ in $A_2^{\mathrm{val}}$ whose image in the completion is $q$ (`hϖ₂`), and assume `HolRingOf ϖ₂ ρ₂` is a domain. Let $s_2$ assign to each away prime a unit of $\mathbb H[\mathbb Q,a_1,b_1]$ and $sf_2$ a finite-idelic unit, subject to `hs₂`: for each away prime $\ell$, the local component of $sf_2(\ell)$ at each $u$ not containing $q$ is $s_2(\ell)\otimes 1$, its local component at each $u$ containing $q$ is $1$, the product of the diagonal image of the scalar $\ell$ with $sf_2(\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` when $\ell\mid N$ and in `primeHeckeSet (meetOrder R₁ n₁) ℓ` otherwise, and $\mathrm{nrd}(s_2(\ell))=\ell$. Let $\Gamma_2$ assign subgroups of $\mathbb H[\mathbb Q,a_1,b_1]^\times$ to the objects of the tower index set, with `hΓ₂0`: $\Gamma_2(\ast)$ consists of the $x$ lying in `CosetGraph.awayUnits R₁ v₂` whose reduced norm has even $q$-adic valuation, and `hΓ₂ℓ`: $\Gamma_2(\ell)=\Gamma_2(\ast)\cap s_2(\ell)\Gamma_2(\ast)s_2(\ell)^{-1}$. Let $w_2,\overline w_2$ assign units to the objects, with `hw₂`: $w_2(\ast)\in$ `awayUnits R₁ v₂` and $\mathrm{nrd}(w_2(\ast))=q$, and for each away prime $\ell$, $w_2(\ell)\in$ `awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` with reduced norm $q$; and `hwbar₂`: $\mathrm{nrd}(\overline w_2(\ast))=q'$, the local image of $\overline w_2(\ast)$ at each $u\ne v_2$ not containing $q'$ lies in [`Submodule.localBoxUnits R₁ u`](def/Submodule_LocalBox.html#L45), and for each $u\ne v_2$ conjugation by $\overline w_2(\ast)$ preserves both `localBox R₁ u` and `localBox Λ₁ u` (each as an equivalence), together with the same three clauses for each $\overline w_2(\ell)$ with `meetOrder R₁ (sf₂ ℓ)` in place of $R_1$.
--
--   Conclusion. There exist a homomorphism $\chi_2$ from the decomposition subgroup of $A_2$ over $\mathbb Q$ to $\mathrm{Multiplicative}(\mathbb Z/2)$ and, for each object $j$ of the tower index set, a ring homomorphism $\iota M_2(j)\colon\mathbb T.\mathrm{objField}(j)\to\operatorname{Frac}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$, such that
--   $$\mathrm{DescentIntertwiningBase}\;q\;0\;1\;A_2\;\rho_2\;\varpi_2\;\Gamma_2\;w_2\;\overline w_2\;s_2\;dIso_2\;M.\overline F\;\mathbb T\;(M.\mathrm{gal}\circ\mathrm{incl})\;(\ell\mapsto galT_\ell\circ\mathrm{incl})\;W\;WT\;\chi_2\;\iota M_2$$
--   holds, the Galois homomorphisms being restricted along the inclusion of the decomposition subgroup, and the Atkin–Lehner indices being $0$ at $q$ and $1$ at $q'$. Among the clauses of this predicate: $\chi_2$ is trivial on the inertia subgroup of $A_2$ over $\mathbb Q$; $\chi_2(\phi)\ne 1$ for every $\phi$ in the decomposition subgroup that is a Frobenius at $q$ for $A_2$; $\chi_2(\tau)=1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_2$ with $x^{q^2}=x$; $\iota M_2(\ast)$ sends the image of $z\in\overline{\mathbb Q}$ in $\mathbb T.\mathrm{objField}(\ast)$ to the image of $z$ in $A_2^{\mathrm{val}}$ under the structure map into $\operatorname{Frac}(\mathrm{HolRingOf}\,\varpi_2\,\rho_2)$; the subfield generated by the image of $A_2^{\mathrm{val}}$ together with the range of $\iota M_2(\ast)$ is the invariant field `Mumford.invariantFieldOf` of $\Gamma_2(\ast)$ acting on $\mathrm{HolRingOf}\,\varpi_2\,\rho_2$; finite families in $\mathbb T.\mathrm{objField}(\ast)$ that are linearly independent over $\overline{\mathbb Q}$ have $\iota M_2(\ast)$-images linearly independent over $A_2^{\mathrm{val}}$; and the remaining clauses impose the intertwining of the semilinear actions of the decomposition group and of the involutions $W$, $WT$ on the tower fields with the uniformisation through $\iota M_2$, $\chi_2$, $\Gamma_2$, $w_2$, $\overline w_2$ and $s_2$.
--
--   This is the Čerednik–Drinfel'd uniformisation step for the Shimura curve $X^{qq'}_0(N)$ and its Hecke tower at the place over $q$: from a rigid, oriented moduli witness for a model $M$ and from the class-set data of the definite quaternion algebra ramified exactly at $q'$, it produces the descent datum (a quadratic character $\chi_2$ of the decomposition group and embeddings of the tower function fields into the fraction field of the holomorphic ring of the $p$-adic upper half plane) satisfying `DescentIntertwiningBase` with Atkin–Lehner indices $0$ at $q$ and $1$ at $q'$. It is used by [`CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero), which combines it with the mirror statement at $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_zero_one_of_two_mul_dvd_of_neZero.lean

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_QMModuliPropsD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_zero_one_of_two_mul_dvd_of_neZero
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
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)

    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ))
    (w : M.ModuliWitnessD Λ N q q' D)
    (horient : w.IsOriented)

    [hXint : AlgebraicGeometry.IsIntegral w.X]
    (hpts : ∃ (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) M.Fbar)
        (e𝔐 : Quiver.Hom 𝔐.C (CategoryTheory.Limits.pullback w.πX w.sbar)) (_ : CategoryTheory.IsIso e𝔐),
        CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.snd w.πX w.sbar) = 𝔐.toBase ∧
        (∀ x : {p : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ))) 𝔐.C //
            CategoryTheory.CategoryStruct.comp p 𝔐.toBase =
              CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)))},
          (w.pts (𝔐.pointEquivPlace x)).1 =
            CategoryTheory.CategoryStruct.comp x.1
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar))) ∧
        (∀ (U : w.X.Opens) [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme U)]
          [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U))]
          (t : w.X.presheaf.obj (Opposite.op U)),
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U)
            (((CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).app U).hom t)) =
          M.toBar (w.eF.symm (w.X.germToFunctionField U t))))
    (ε : Nat.Primes → ℤˣ) (hε : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1)
    (𝕋 : HeckeTower.TowerData q q' M.Fbar)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    (hgalT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (hgalT_φ : ∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M.Fbar),
      galT α.1 σ • 𝕋.φ α x = 𝕋.φ α (M.gal σ • x))
    (hW_base : ∀ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) a = a)
    (hWT_base : ∀ ℓ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) a = a)
    (hW_sq : ∀ i, W i * W i = 1)
    (hW_comm : W 0 * W 1 = W 1 * W 0)
    (hW_gal : ∀ i σ, W i * M.gal σ = M.gal σ * W i)
    (hWT_sq : ∀ ℓ i, WT ℓ i * WT ℓ i = 1)
    (hWT_comm : ∀ ℓ, WT ℓ 0 * WT ℓ 1 = WT ℓ 1 * WT ℓ 0)
    (hWT_gal : ∀ ℓ i σ, WT ℓ i * galT ℓ σ = galT ℓ σ * WT ℓ i)
    (hWT_φ : ∀ (α : HeckeTower.Arr q q') i (x : M.Fbar), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x))
    (hW0_pic : ∀ c : M.J, W 0 • c = ((ε ⟨q, Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q Fact.out c)
    (hW1_pic : ∀ c : M.J, W 1 • c = ((ε ⟨q', Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q' Fact.out c)

    (hW0_pl : ∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q Fact.out (Finsupp.single P 1) = Finsupp.single (W 0 • P) 1)
    (hW1_pl : ∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q' Fact.out (Finsupp.single P 1) = Finsupp.single (W 1 • P) 1)
    (hdeg : ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α)
    (hhecke : ∀ (ℓ : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) M.Fbar),
      M.corrBar ℓ.1 ℓ.1.prop D = Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D)

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
    :
    (∃ (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂)),
        CerednikDrinfeld.DescentIntertwiningBase q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
          M.Fbar 𝕋 (M.gal.comp (A₂.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₂.decompositionSubgroup ℚ).subtype) W WT χ₂ ιM₂) := by sorry
