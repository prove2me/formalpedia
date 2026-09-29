-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/6e0b7261-271c-5e88-a12a-a6a06193b819
-- title:
--   Descent intertwining base above q' from an oriented moduli witness
-- statement:
--   Numerical and local data. Fix a nonzero squarefree $N$, two distinct primes $q$ and $q'$, both at least $5$ and neither dividing $N$, and a nonzero $D$ with $2Nqq' \mid D$. Fix a valuation subring $A_1$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` such that $q'$ is a non-unit of $A_1$ (`A₁.LiesOverPrime q'`), and assume `A₁.DecompositionIsometric ℚ`: every element of the decomposition subgroup of $A_1$ over $\mathbb Q$ preserves `A₁.valuation`. Fix also a height-one prime $v_1$ of $\mathcal O_{\mathbb Q}$ containing $q'$.
--
--   The definite side. Rationals $a_2, b_2$ are given with `IsDefiniteRamifiedExactlyAt q`, i.e. $a_2 < 0$, $b_2 < 0$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ all nonzero elements of $\mathbb H[\mathbb Q, a_2, b_2] \otimes_{\mathbb Q} \mathbb Q_v$ are units exactly when $q \in v$. Submodules $\Lambda_2, R_2 \subseteq \mathbb H[\mathbb Q,a_2,b_2]$ are given with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first) and $R_2 \le \Lambda_2$. A finite-adelic unit $n_2$ is given lying in `primeHeckeSet R₂ q'`: $n_2$ lies in the finite-adelic box of $R_2$, so does $q' \cdot n_2^{-1}$, while $n_2^{-1}$ and $q'^{-1} n_2$ do not. Writing `meetOrder R₂ n₂` $= R_2 \cap n_2 R_2 n_2^{-1}$ (the conjugate being formed inside the adelic box), the hypotheses are: `hS₂`, that `meetOrder R₂ n₂` is an Eichler order of level $Nq'$; `hnorm₂`, that conjugation by $n_2$ preserves it; `hsq₂`, that the shift by $n_2$ on the double coset class set of the finite-idele stabiliser of `meetOrder R₂ n₂` is an involution; and `hlaws₂`, the four clauses of `ClassSetHeckeLaws N q' Λ₂ R₂ n₂` (with $q'$ as distinguished prime): the edge Hecke operators commute pairwise, the vertex Hecke operators commute pairwise, for primes $\ell \neq q'$ and $i \in \mathrm{Fin}\,2$ the degeneracy maps `jointDelta` intertwine edge with vertex Hecke operators, and the edge operators preserve the common kernel of the `jointDelta` maps.
--
--   The indefinite side. Rationals $a,b$ are given with `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly at the places $v$ containing $q$ or $q'$. Here $R$ is an Eichler order of level $N$, $\iota$ an injective $\mathbb Q$-algebra map into $M_2(\mathbb R)$, and $\Lambda \supseteq R$ a maximal order. $M$ is a `ShimuraCurveModel` for $(R,\iota)$ with Hecke sets `levelHeckeUSet Λ R ℓ` at primes $\ell \mid N$ (those $h$ in `primeHeckeSet R ℓ` with $h R h^{-1} \neq R$ and $R \not\le h \Lambda h^{-1}$) and `primeHeckeSet R ℓ` otherwise; thus $M$ carries function fields $M.F$ over $\mathbb Q$ and $M.\mathrm{Fbar}$ over $\overline{\mathbb Q}$, the map `M.toBar`, a semilinear Galois action `M.gal`, divisor correspondences `M.corrBar ℓ` and the group `M.J` with operators `M.heckePic0 ℓ`.
--
--   The moduli witness. $w$ is a `ModuliWitnessD` for $M$, $\Lambda$, $N$, $q$, $q'$, $D$: a scheme $w.X$, smooth and proper over $\mathrm{Spec}\,\mathbb Z[1/D]$ via $w.\pi_X$, a geometric point $w.\overline s$ over $\overline{\mathbb Q}$, maps $w.\mathrm{pt}$ sending fake elliptic curves with $\Lambda$-action and level-$N$ structure over a ring to points of $w.\pi_X$, an isomorphism $w.e_F$ from $M.F$ to the function field of $w.X$, a bijection $w.\mathrm{pts}$ between places of $M.\mathrm{Fbar}$ and $\overline s$-points, together with the invariance, base-change, surjectivity and injectivity clauses of that structure. The hypothesis `horient` is `w.IsOriented`: for every prime $\ell \mid N$ and places $P, Q$ of $M.\mathrm{Fbar}$, $Q$ lies in the support of `M.corrBar ℓ` applied to $P$ if and only if there are $u$ with an extra level structure at $\ell$ and $d$ such that $u$ and $d$ represent the points $w.\mathrm{pts}\,P$ and $w.\mathrm{pts}\,Q$ and $u \to d$ is a level isogeny at $\ell$. The scheme $w.X$ is assumed integral, and `hpts` asserts that the geometric fibre is rigidified by a curve model: there are a `CurveModel` $\mathfrak M$ of $M.\mathrm{Fbar}$ over $\overline{\mathbb Q}$ and an isomorphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to the pullback of $w.\pi_X$ along $w.\overline s$ such that $e_{\mathfrak M}$ followed by the second projection is $\mathfrak M.\mathrm{toBase}$, such that for every $\overline{\mathbb Q}$-point $x$ of $\mathfrak M.C$ over the base the point $w.\mathrm{pts}$ of the corresponding place is $x$ followed by $e_{\mathfrak M}$ followed by the first projection, and such that on every open $U$ of $w.X$ and section $t$ over it, transporting the germ of the pullback of $t$ along $e_{\mathfrak M}$ followed by the first projection through $\mathfrak M.\mathrm{ffEquiv}^{-1}$ gives the image under `M.toBar` of the germ of $t$ read through $w.e_F^{-1}$.
--
--   The Hecke tower and the involutions. Signs $\varepsilon(\ell) \in \mathbb Z^{\times}$ are given, equal to $1$ for $\ell \neq q, q'$. $\mathbb T$ is a `TowerData` over $M.\mathrm{Fbar}$ for the primes away from $q, q'$: for each such $\ell$ a curve field $\mathbb T.F\,\ell$ over $\overline{\mathbb Q}$ together with two finite integral $\overline{\mathbb Q}$-algebra maps $\mathbb T.\varphi(\ell,i)$, $i \in \mathrm{Fin}\,2$, from $M.\mathrm{Fbar}$. The hypothesis `hfg` requires each field $\mathbb T.\mathrm{objField}\,j$ ($j$ either the base $M.\mathrm{Fbar}$ or some $\mathbb T.F\,\ell$) to contain an element transcendental over $\overline{\mathbb Q}$ over which it is finite. Semilinear automorphism data are given: Galois actions $\mathrm{gal}^{\mathbb T}_{\ell}$ on $\mathbb T.F\,\ell$ whose base automorphisms are the given $\sigma$ (`hgalT_base`) and which are compatible with the degeneracy maps (`hgalT_φ`: $\mathrm{gal}^{\mathbb T}_{\alpha_1}(\sigma) \cdot \mathbb T.\varphi\alpha\,x = \mathbb T.\varphi\alpha(M.\mathrm{gal}(\sigma) \cdot x)$); involutions $W_0, W_1$ on $M.\mathrm{Fbar}$ and $W^{\mathbb T}_{\ell,i}$ on $\mathbb T.F\,\ell$ acting trivially on $\overline{\mathbb Q}$ (`hW_base`, `hWT_base`), each of square $1$ (`hW_sq`, `hWT_sq`), commuting with one another at each level (`hW_comm`, `hWT_comm`), commuting with the Galois actions (`hW_gal`, `hWT_gal`) and compatible with the degeneracy maps (`hWT_φ`). Furthermore $W_0$ acts on $M.J$ as $\varepsilon(q)$ times `M.heckePic0 q` and $W_1$ as $\varepsilon(q')$ times `M.heckePic0 q'` (`hW0_pic`, `hW1_pic`); on divisors, `M.corrBar q` sends the divisor of a place $P$ to that of $W_0 \cdot P$ and `M.corrBar q'` to that of $W_1 \cdot P$ (`hW0_pl`, `hW1_pl`); the degrees satisfy $\operatorname{finrankAlong}(\mathbb T.\varphi\alpha) = \ell$ if $\ell \mid N$ and $\ell + 1$ otherwise, for $\alpha$ with first component $\ell$ (`hdeg`); and for every away prime $\ell$ the correspondence `M.corrBar ℓ` on divisors of $M.\mathrm{Fbar}$ is pullback along $\mathbb T.\varphi(\ell,0)$ followed by pushforward along $\mathbb T.\varphi(\ell,1)$ (`hhecke`).
--
--   The $p$-adic uniformisation data at $q'$. Let $K_1 =$ [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13), the topological closure of the prime field inside the completion of `A₁.valuation`. An injective $\mathbb Q$-algebra map $\iota_1 : \mathbb H[\mathbb Q,a_2,b_2] \to M_2(K_1)$ is given, together with $\rho_1 : \mathbb H[\mathbb Q,a_2,b_2]^{\times} \to \mathrm{PGL}_2(K_1)$ defined by passing $\iota_1$ to the projective group (`hρ₁`), and a pseudo-uniformiser $\varpi_1$ of $K_1$ in the completion whose image in the completion is $q'$ (`hϖ₁`); the ring `Omega.HolRingOf ϖ₁ ρ₁` is assumed to be a domain. Elements $s_1(\ell) \in \mathbb H[\mathbb Q,a_2,b_2]^{\times}$ and finite-adelic units $sf_1(\ell)$, indexed by the primes away from $q, q'$, satisfy `hs₁`: at each place $u$ not containing $q'$ the local component of $sf_1(\ell)$ is $s_1(\ell) \otimes 1$; at each place containing $q'$ it is $1$; the diagonal finite idele of the central unit $\ell$ times $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` when $\ell \mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise; and $\mathrm{nrd}(s_1(\ell)) = \ell$. Subgroups $\Gamma_1(j)$ are given with $\Gamma_1(\mathrm{none})$ the set of $x$ in `CosetGraph.awayUnits R₂ v₁` (unit at every place other than $v_1$ for the local box of $R_2$) with $\mathrm{ord}_{q'}(\mathrm{nrd}\,x)$ even, and $\Gamma_1(\ell) = \Gamma_1(\mathrm{none}) \cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$. Elements $w_1(j), \overline w_1(j)$ are given with: $w_1(\mathrm{none})$ in `awayUnits R₂ v₁` of reduced norm $q'$, and $w_1(\ell)$ in `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` of reduced norm $q'$ (`hw₁`); and, in `hwbar₁`, $\overline w_1(\mathrm{none})$ of reduced norm $q$, locally a unit of the box of $R_2$ at every place $u \neq v_1$ not containing $q$, and with conjugation by it preserving membership in the local boxes of $R_2$ and of $\Lambda_2$ at all places $u \neq v_1$, the same three conditions being imposed on $\overline w_1(\ell)$ with `meetOrder R₂ (sf₁ ℓ)` in place of $R_2$. Finally $d\mathrm{Iso}_1$ is a homomorphism from the decomposition subgroup of $A_1$ over $\mathbb Q$ to the isometric automorphisms of the completion, whose underlying ring equivalence is the natural action (`hdIso₁`).
--
--   Conclusion. Under these hypotheses there exist a homomorphism $\chi_1$ from the decomposition subgroup of $A_1$ over $\mathbb Q$ to $\mathrm{Multiplicative}(\mathbb Z/2)$ and, for every object $j$ of the tower, a ring homomorphism $\iota_{M,1}(j)$ from $\mathbb T.\mathrm{objField}\,j$ into the fraction field of `Omega.HolRingOf ϖ₁ ρ₁`, such that
--   $$\mathtt{DescentIntertwiningBase}\ q'\ 1\ 0\ A_1\ \rho_1\ \varpi_1\ \Gamma_1\ w_1\ \overline w_1\ s_1\ d\mathrm{Iso}_1\ M.\mathrm{Fbar}\ \mathbb T\ \mathrm{gal}_0\ \mathrm{gal}^{\mathbb T}\ W\ W^{\mathbb T}\ \chi_1\ \iota_{M,1}$$
--   holds, where the distinguished residue parameter is $r = q'$, the two indices of $\mathrm{Fin}\,2$ are $1$ and $0$ in that order, and $\mathrm{gal}_0$, $\mathrm{gal}^{\mathbb T}$ are the restrictions of `M.gal` and of the $\mathrm{gal}^{\mathbb T}_{\ell}$ to the decomposition subgroup. Explicitly, the clauses of this predicate assert: $\chi_1$ is trivial on the inertia subgroup of $A_1$ over $\mathbb Q$; $\chi_1(\varphi) \neq 1$ for every $\varphi$ that is a Frobenius element of $A_1$ at $q'$; $\chi_1(\tau) = 1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2} = x$; the composite of $\iota_{M,1}(\mathrm{none})$ with the structure map $\overline{\mathbb Q} \to M.\mathrm{Fbar}$ agrees with the inclusion of $\overline{\mathbb Q}$ into the completion followed by the map of the completion into the fraction field; the subfield generated by the image of the completion together with the image of $\iota_{M,1}(\mathrm{none})$ is the $\Gamma_1(\mathrm{none})$-invariant field `Mumford.invariantFieldOf` of the completion, the unit group of $\mathbb H[\mathbb Q,a_2,b_2]$ and `Omega.HolRingOf ϖ₁ ρ₁`; $\iota_{M,1}(\mathrm{none})$ carries any finite subset of $M.\mathrm{Fbar}$ that is linearly independent over $\overline{\mathbb Q}$ to a family linearly independent over the completion; and the remaining clauses, summarised here, impose conditions, starting with one on pairs consisting of an element $\tau$ of the decomposition subgroup and an element of $M.\mathrm{Fbar}$, that relate the embeddings $\iota_{M,1}$ to the semilinear actions $\mathrm{gal}_0$, $\mathrm{gal}^{\mathbb T}$, the involutions $W$, $W^{\mathbb T}$, the character $\chi_1$ and the uniformisation data $A_1, \rho_1, \varpi_1, \Gamma_1, w_1, \overline w_1, s_1, d\mathrm{Iso}_1$.
--
--   This is the Čerednik–Drinfeld $p$-adic uniformisation input at the place above $q'$: from a rigidified, oriented moduli witness for a model of the Shimura curve of level $N$ attached to the indefinite quaternion algebra ramified exactly at $\{q,q'\}$, together with class-set Hecke data for the definite algebra ramified exactly at $q$, it produces the quadratic character and the compatible embeddings of the whole Hecke tower of function fields into the fraction field of the Mumford holomorphic ring, i.e. the descent datum for the uniformisation at $q'$. It supplies the conjunct at the place above $q'$ in the construction [`CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero), whose mirror statement performs the interchange of the roles of $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero.lean

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

theorem CerednikDrinfeld.exists_descentIntertwiningBase_of_rigidOrientedModuliWitness_one_zero_of_two_mul_dvd_of_neZero
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
          M.Fbar 𝕋 (M.gal.comp (A₁.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₁.decompositionSubgroup ℚ).subtype) W WT χ₁ ιM₁) := by sorry
