-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/5038948f-6972-58cc-a37d-4d518beb158d
-- title:
--   Čerednik interchange and Hecke tower for X^{qq'}₀(N)
-- statement:
--   Throughout, $\overline{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and for rationals $a,b$ the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ is written with its reduced norm `nrd`.
--
--   **Global numerical data.** A nonzero natural number $N$ that is squarefree, two primes $q \neq q'$ with $q,q' \geq 5$ and $q \nmid N$, $q' \nmid N$, and a nonzero natural number $D$ divisible by $6Nqq'$. Two valuation subrings $A_1, A_2$ of $\overline{\mathbb Q}$ are fixed, with $q'$ a nonunit of $A_1$ and $q$ a nonunit of $A_2$ (the predicate `LiesOverPrime`).
--
--   **The definite datum used at $A_1$.** Rationals $a_2,b_2$ with `IsDefiniteRamifiedExactlyAt q`, i.e. $a_2<0$, $b_2<0$ and, for every height-one prime $v$ of the integers of $\mathbb Q$, the algebra $B_2 \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra precisely when $q \in v$, where $B_2 = \mathbb H[\mathbb Q,a_2,b_2]$. Further: $\mathbb Z$-lattices $\Lambda_2 \supseteq R_2$ in $B_2$ with $\Lambda_2$ a maximal order and $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first); a finite idele $n_2 \in$ `primeHeckeSet R₂ q'`, that is, $n_2$ lies in the finite adelic box of $R_2$, $q'n_2^{-1}$ lies in that box, while $n_2^{-1}$ and $(q')^{-1}n_2$ do not; the order `meetOrder R₂ n₂` $= R_2 \cap n_2R_2n_2^{-1}$ is Eichler of level $Nq'$ (`hS₂`) and is stable under conjugation by $n_2$ (`hnorm₂`); the shift by $n_2$ on the class set of the finite-idele stabiliser of `meetOrder R₂ n₂` is an involution (`hsq₂`); the two relevant class sets are finite; and `hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂`, whose four clauses assert that the edge Hecke matrices at all primes commute pairwise, that the vertex Hecke matrices commute pairwise, that for every prime $\ell \neq q'$ the two degeneracy pushforwards carry the edge Hecke matrix at $\ell$ to the vertex Hecke matrix at $\ell$, and that the edge Hecke matrices preserve the common kernel of the two degeneracy pushforwards.
--
--   **The definite datum used at $A_2$.** The mirror-image data with $q$ and $q'$ exchanged: rationals $a_1,b_1$ with `IsDefiniteRamifiedExactlyAt q'` for $B_1 = \mathbb H[\mathbb Q,a_1,b_1]$; $\Lambda_1 \supseteq R_1$ with $\Lambda_1$ maximal and $R_1$ Eichler of level $N$; $n_1 \in$ `primeHeckeSet R₁ q` with `meetOrder R₁ n₁` Eichler of level $Nq$, stable under conjugation by $n_1$, the shift by $n_1$ on the corresponding class set an involution, the class sets finite, and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁`.
--
--   **The indefinite datum.** Rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and $B \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra precisely when $q \in v$ or $q' \in v$, where $B = \mathbb H[\mathbb Q,a,b]$. In $B$ an Eichler order $R$ of level $N$ is fixed, together with an injective $\mathbb Q$-algebra map $\iota : B \to M_2(\mathbb R)$.
--
--   **The Mumford-side datum at $A_1$ (uniformisation at the place over $q'$, using $B_2$).** The valuation of $A_1$ is invariant under the decomposition subgroup over $\mathbb Q$ (`DecompositionIsometric`, as a `Fact`); $v_1$ is a height-one prime containing $q'$; $\iota_1 : B_2 \to M_2(K_1)$ is an injective $\mathbb Q$-algebra map, where $K_1 =$ [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13) is the topological closure of the prime subfield in the completion $C_1 =$ `A₁.valuation.Completion`, and $\rho_1 : B_2^\times \to \mathrm{PGL}_2(K_1)$ is the projectivisation of $\iota_1$ (`hρ₁`); $\varpi_1$ is a pseudo-uniformiser of $C_1$ over $K_1$ whose image in $C_1$ is $q'$ (`hϖ₁`), and the ring `Omega.HolRingOf ϖ₁ ρ₁` of rigid-holomorphic functions on the Drinfeld upper half plane is a domain. For each prime $\ell \notin \{q,q'\}$ (the type `HeckeTower.AwayPrime q q'`) there are $s_1(\ell) \in B_2^\times$ and a finite idele $sf_1(\ell)$ subject to the four clauses of `hs₁`: the component of $sf_1(\ell)$ at every prime $u$ not containing $q'$ is $s_1(\ell) \otimes 1$; its component at every $u$ containing $q'$ is $1$; the product of the diagonal idele of the scalar $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell \mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise (the former being those elements of the latter Hecke set which do not normalise `meetOrder R₂ n₂` and for which `meetOrder R₂ n₂` is not contained in the corresponding conjugate of $\Lambda_2$); and $\mathrm{nrd}(s_1(\ell)) = \ell$. A family of subgroups $\Gamma_1$ of $B_2^\times$ indexed by `HeckeTower.Obj q q'` $=$ `Option (AwayPrime q q')` is given, with $\Gamma_1(\mathrm{none})$ the set of units lying in `CosetGraph.awayUnits R₂ v₁` (the intersection, over all primes $w \neq v_1$, of the preimages under the local map at $w$ of the subgroup generated by the local box units of $R_2$ at $w$) whose reduced norm has even $q'$-adic valuation (`hΓ₁0`), and $\Gamma_1(\mathrm{some}\ \ell) = \Gamma_1(\mathrm{none}) \cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$ (`hΓ₁ℓ`). Two further families $w_1, \bar w_1$ of units of $B_2$ indexed by the same type satisfy: `hw₁`, that $w_1(\mathrm{none})$ lies in `awayUnits R₂ v₁` with reduced norm $q'$ and, for each $\ell$, $w_1(\mathrm{some}\ \ell)$ lies in `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; and `hwbar₁`, that $\bar w_1(\mathrm{none})$ has reduced norm $q$, its image in the local algebra at $u$ is a local box unit of $R_2$ for every $u \neq v_1$ not containing $q$, and conjugation by it on the local algebra at every $u \neq v_1$ preserves both the local box of $R_2$ and the local box of $\Lambda_2$ (as an equivalence, in both directions), with the same three conditions for each $\bar w_1(\mathrm{some}\ \ell)$, the order $R_2$ being replaced by `meetOrder R₂ (sf₁ ℓ)`. Finally $dIso_1$ realises the decomposition subgroup of $A_1$ over $\mathbb Q$ inside the isometric automorphisms of $C_1$ over $K_1$, its underlying ring isomorphism being the Galois action (`hdIso₁`).
--
--   **The Mumford-side datum at $A_2$.** The same package with the roles of $q$ and $q'$ exchanged: $v_2$ contains $q$; $\iota_2, \rho_2$ are built from $B_1$ over $K_2 =$ `ratClosure A₂`; $\varpi_2$ has image $q$ in the completion of $A_2$ and `Omega.HolRingOf ϖ₂ ρ₂` is a domain; $s_2, sf_2$ satisfy the four clauses of `hs₂` with truncation at the primes containing $q$ and Hecke sets formed from $\Lambda_1$ and `meetOrder R₁ n₁`; $\Gamma_2$ is described through `awayUnits R₁ v₂` and evenness of the $q$-adic valuation of the reduced norm, with the same conjugation recipe at level $\ell$; $w_2$ has reduced norm $q$ and $\bar w_2$ reduced norm $q'$, with the local conditions at the primes $u \neq v_2$; and $dIso_2$ is as before.
--
--   **Conclusion.** There exist a maximal order $\Lambda$ in $B$ with $R \leq \Lambda$ and a `ShimuraCurveModel` $M$ for $R$, $\iota$ and the level family $\ell \mapsto$ `levelHeckeUSet Λ R ℓ` if $\ell \mid N$, `primeHeckeSet R ℓ` otherwise, and a sign function $\varepsilon :$ `Nat.Primes` $\to \mathbb Z^\times$, such that:
--
--   1. $\varepsilon(\ell) = 1$ for every prime $\ell$ other than $q$ and $q'$;
--
--   2. for every prime $p$, `M.GoodReductionOutside p (D * p)` holds: for every prime $\ell \nmid Dp$ and every valuation subring $\mathcal B$ of $\overline{\mathbb Q}$ lying over $\ell$, the inertia subgroup of $\mathcal B$ over $\mathbb Q$ acts trivially on the $p$-torsion of `M.J`, and for every $\sigma$ that is a Frobenius at $\ell$ for $\mathcal B$ the Eichler–Shimura relation $\sigma^2 t - T_\ell(\sigma t) + \ell\, t = 0$ holds for every $p$-torsion $t$ in `M.J`;
--
--   and there exists a `HeckeTower.TowerData` $\mathbb T$ for $(q,q')$ over `M.Fbar`, i.e. for each prime $\ell \notin \{q,q'\}$ a curve field $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$ with two finite integral $\overline{\mathbb Q}$-algebra maps $\mathbb T.\varphi(\ell,i)$ from `M.Fbar`, such that, writing $\mathbb T.\mathrm{objField}(\mathrm{none}) =$ `M.Fbar` and $\mathbb T.\mathrm{objField}(\mathrm{some}\ \ell) = \mathbb T.F(\ell)$:
--
--   <ol start="3">
--   each $\mathbb T.\mathrm{objField}(j)$ contains an element transcendental over $\overline{\mathbb Q}$ over whose adjunction the field is finite-dimensional;
--
--   and there exist Galois actions $galT(\ell)$ of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ by semilinear automorphisms of $\mathbb T.F(\ell)$, a pair $W : \mathrm{Fin}\ 2 \to$ `SemilinearAut (AlgebraicClosure ℚ) M.Fbar` and pairs $WT(\ell)$ of semilinear automorphisms of $\mathbb T.F(\ell)$, with:
--
--   <ol start="4">
--   the base automorphism of $galT(\ell)(\sigma)$ equal to $\sigma$ for all $\ell$ and $\sigma$;
--   for every arrow $\alpha = (\ell,i)$, every $\sigma$ and every $x$ in `M.Fbar`, $galT(\ell)(\sigma) \cdot \mathbb T.\varphi(\alpha)(x) = \mathbb T.\varphi(\alpha)(M.\mathrm{gal}(\sigma)\cdot x)$;
--   all $W(i)$ and all $WT(\ell)(i)$ act trivially on the base field $\overline{\mathbb Q}$;
--   $W(i)^2 = 1$, $W(0)W(1) = W(1)W(0)$, and each $W(i)$ commutes with every $M.\mathrm{gal}(\sigma)$;
--   $WT(\ell)(i)^2 = 1$, $WT(\ell)(0)WT(\ell)(1) = WT(\ell)(1)WT(\ell)(0)$, and each $WT(\ell)(i)$ commutes with every $galT(\ell)(\sigma)$;
--   for every arrow $\alpha$, every $i$ and every $x$ in `M.Fbar`, $WT(\alpha_1)(i)\cdot \mathbb T.\varphi(\alpha)(x) = \mathbb T.\varphi(\alpha)(W(i)\cdot x)$;
--   on `M.J`, $W(0)$ acts as $\varepsilon(q)$ times `M.heckePic0 q` and $W(1)$ as $\varepsilon(q')$ times `M.heckePic0 q'`;
--   for every arrow $\alpha$, `finrankAlong` of $\mathbb T.\varphi(\alpha)$ equals `HeckeTower.arrowDegree N α`, namely $\ell$ if $\ell \mid N$ and $\ell+1$ otherwise, where $\ell = \alpha_1$;
--   for every prime $\ell \notin \{q,q'\}$ and every divisor $E$ of `M.Fbar` over $\overline{\mathbb Q}$, `M.corrBar ℓ E` is the divisor correspondence obtained by pulling $E$ back along $\mathbb T.\varphi(\ell,0)$ and pushing the result forward along $\mathbb T.\varphi(\ell,1)$;
--   there exist a homomorphism $\chi_1$ from the decomposition subgroup of $A_1$ over $\mathbb Q$ to $\mathrm{Multiplicative}(\mathbb Z/2)$ and, for each $j$, a ring homomorphism $\iota M_1(j) : \mathbb T.\mathrm{objField}(j) \to \mathrm{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ such that `DescentIntertwiningBase` holds with $r = q'$, involution indices $1$ and $0$, the data $A_1, \rho_1, \varpi_1, \Gamma_1, w_1, \bar w_1, s_1, dIso_1$, the field `M.Fbar`, the tower $\mathbb T$, the restrictions of $M.\mathrm{gal}$ and of the $galT(\ell)$ to the decomposition subgroup, $W$, $WT$, $\chi_1$ and $\iota M_1$; this predicate requires that $\chi_1$ be trivial on inertia, nontrivial at every Frobenius at $q'$, and trivial exactly on those $\tau$ fixing all elements $x$ of the residue field of $A_1$ with $x^{q'^2} = x$; that $\iota M_1(\mathrm{none})$ restrict on $\overline{\mathbb Q}$ to the inclusion into the completion, that the subfield generated by the completion together with the image of $\iota M_1(\mathrm{none})$ be the $\Gamma_1(\mathrm{none})$-invariant subfield of $\mathrm{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ in the sense of `Mumford.invariantFieldOf`, and that $\iota M_1(\mathrm{none})$ carry $\overline{\mathbb Q}$-linearly independent finite families to families independent over the completion; together with further clauses of the same kind intertwining the action of the decomposition group, the involutions indexed by $1$ and $0$, and the maps of the tower with the Mumford-quotient data;
--   the corresponding statement at $A_2$: there exist $\chi_2$ and embeddings $\iota M_2(j)$ into $\mathrm{Frac}(\mathrm{HolRingOf}\ \varpi_2\ \rho_2)$ for which `DescentIntertwiningBase` holds with $r = q$, involution indices $0$ and $1$, and the data $A_2, \rho_2, \varpi_2, \Gamma_2, w_2, \bar w_2, s_2, dIso_2$, the same $M$, $\mathbb T$, $W$ and $WT$.
--
--   The two indices $0$ and $1$ of $W$ are thus attached to $q$ and $q'$ respectively, in accordance with clause 10 and with the index data in clauses 13 and 14.
--
--   This is the Čerednik–Drinfeld $p$-adic uniformisation of the Shimura curve attached to an Eichler order of level $N$ in the indefinite quaternion algebra of discriminant $qq'$, at both ramified primes simultaneously: the interchange of local invariants with its Frobenius-twisted descent datum, packaged with a canonical model over $\mathbb Q$ with good reduction away from $D$, the two Atkin–Lehner involutions and their identification with the Hecke operators at $q$ and $q'$ on the Jacobian, and the prime-to-$qq'$ Hecke tower of degeneracy maps. It is the base-level ($\Gamma_0(N)$) input to [`CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero), which propagates the constant-field, Galois and Atkin–Lehner clauses to the levels $N\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchangeBase_pair_of_six_mul_dvd_of_neZero
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

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
    ∃ (Λ : Submodule ℤ ℍ[ℚ, a, b]) (_ : IsMaximalOrder Λ) (_ : R ≤ Λ),
    ∃ M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
      ∃ ε : Nat.Primes → ℤˣ, (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1) ∧
      (∀ p : ℕ, p.Prime → M.GoodReductionOutside p (D * p)) ∧

      ∃ (𝕋 : HeckeTower.TowerData q q' M.Fbar)

        (_ : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
          FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))

        (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

        (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ)),
        (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
        (∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M.Fbar),
          galT α.1 σ • 𝕋.φ α x = 𝕋.φ α (M.gal σ • x)) ∧
        (∀ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) a = a) ∧ (∀ ℓ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) a = a) ∧
        (∀ i, W i * W i = 1) ∧ W 0 * W 1 = W 1 * W 0 ∧ (∀ i σ, W i * M.gal σ = M.gal σ * W i) ∧
        (∀ ℓ i, WT ℓ i * WT ℓ i = 1) ∧ (∀ ℓ, WT ℓ 0 * WT ℓ 1 = WT ℓ 1 * WT ℓ 0) ∧ (∀ ℓ i σ, WT ℓ i * galT ℓ σ = galT ℓ σ * WT ℓ i) ∧
        (∀ (α : HeckeTower.Arr q q') i (x : M.Fbar), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x)) ∧

        (∀ c : M.J, W 0 • c = ((ε ⟨q, Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q Fact.out c) ∧
        (∀ c : M.J, W 1 • c = ((ε ⟨q', Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q' Fact.out c) ∧

        (∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α) ∧
        (∀ (ℓ : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) M.Fbar),
          M.corrBar ℓ.1 ℓ.1.prop D = Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D) ∧

      (∃ (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁)),
        CerednikDrinfeld.DescentIntertwiningBase q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
          M.Fbar 𝕋 (M.gal.comp (A₁.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₁.decompositionSubgroup ℚ).subtype) W WT χ₁ ιM₁) ∧

      (∃ (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂)),
        CerednikDrinfeld.DescentIntertwiningBase q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
          M.Fbar 𝕋 (M.gal.comp (A₂.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₂.decompositionSubgroup ℚ).subtype) W WT χ₂ ιM₂) := by sorry
