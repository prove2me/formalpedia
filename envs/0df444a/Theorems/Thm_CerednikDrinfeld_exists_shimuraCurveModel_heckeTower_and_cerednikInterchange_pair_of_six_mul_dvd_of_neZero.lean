-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/fbc64c25-ed10-50c7-b70a-d6060cb0f4e3
-- title:
--   Čerednik interchange at q and q' for X^{qq'}₀(N)
-- statement:
--   Numerical data. Fixed are a non-zero squarefree natural number $N$, two distinct primes $q,q'$ with $q,q'\ge 5$, neither dividing $N$, and a non-zero natural number $D$ divisible by $6Nqq'$. Fixed further are two valuation subrings $A_1,A_2$ of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$ with `A₁.LiesOverPrime q'` and `A₂.LiesOverPrime q`, i.e. $q'$ is a non-unit of $A_1$ and $q$ a non-unit of $A_2$; each of $A_1,A_2$ is assumed to satisfy `DecompositionIsometric`, meaning that every element of its decomposition subgroup over $\mathbb Q$ preserves its valuation.
--
--   The definite algebra ramified at $q$ (block with subscript $2$). Rationals $a_2,b_2$ with `IsDefiniteRamifiedExactlyAt q`: $a_2<0$, $b_2<0$, and for a finite place $v$ of $\mathbb Q$ the algebra $H_2:=\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra precisely when $v$ lies over $q$. Fixed are $\mathbb Z$-submodules $\Lambda_2,R_2$ of $H_2$ with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders of index $N$ in one of them), and $R_2\le\Lambda_2$; a unit $n_2$ of $H_2\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ lying in `primeHeckeSet R₂ q'`, that is, $n_2$ lies in the finite-adelic box of $R_2$, so does $q'\,n_2^{-1}$, while $n_2^{-1}$ and $q'^{-1}n_2$ do not. The hypotheses on the edge order `meetOrder R₂ n₂` $=R_2\cap n_2R_2n_2^{-1}$ are: it is an Eichler order of level $Nq'$; conjugation by $n_2$ returns it; and the shift by $n_2$ on the class set of the stabiliser of its adelic box (the double coset space of global units in finite ideles modulo that stabiliser) is an involution. The class sets occurring are assumed finite. Finally `hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂` asserts four things: the edge Hecke matrices at all primes commute pairwise; the vertex Hecke matrices at all primes commute pairwise; for every prime $\ell\ne q'$ and each $i\in\{0,1\}$ the $i$-th degeneracy pushforward intertwines the edge and vertex Hecke matrices at $\ell$; and for every prime the edge Hecke matrix preserves the joint kernel of the two degeneracy pushforwards.
--
--   The definite algebra ramified at $q'$ (block with subscript $1$). Symmetrically, rationals $a_1,b_1$ with `IsDefiniteRamifiedExactlyAt q'` for $H_1:=\mathbb H[\mathbb Q,a_1,b_1]$, a maximal order $\Lambda_1$, an Eichler order $R_1$ of level $N$ contained in it, a unit $n_1$ of $H_1\otimes\mathbb A^{\mathrm{fin}}_{\mathbb Q}$ in `primeHeckeSet R₁ q`, with `meetOrder R₁ n₁` an Eichler order of level $Nq$, stable under conjugation by $n_1$, the class-set shift by $n_1$ an involution, the class sets finite, and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁`.
--
--   The indefinite algebra. Rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for a finite place $v$ the completion of $B:=\mathbb H[\mathbb Q,a,b]$ at $v$ is a division algebra precisely when $v$ lies over $q$ or over $q'$; an Eichler order $R\subset B$ of level $N$; and an injective $\mathbb Q$-algebra map $\iota:B\to M_2(\mathbb R)$.
--
--   Rigid-analytic and group-theoretic data at $A_1$ (for $H_2$, residue characteristic $q'$). A height-one prime $v_1$ of $\mathcal O_{\mathbb Q}$ containing $q'$; an injective $\mathbb Q$-algebra map $\iota_1:H_2\to M_2(K_1)$, where $K_1=$ [`ValuationSubring.ratClosure A₁`](def/ValuationSubring_CompletionRatClosure.html#L13) is the topological closure of the prime subfield inside the completion of $A_1$ for its valuation; a homomorphism $\rho_1:H_2^\times\to \mathrm{PGL}_2(K_1)$ which on each unit is the class of its image under $\iota_1$; a pseudo-uniformiser $\varpi_1$ of $K_1$ relative to that completion whose image in the completion is $q'$; and the assumption that the ring `Omega.HolRingOf ϖ₁ ρ₁` of rigid-holomorphic functions attached to $\varpi_1,\rho_1$ is a domain. For every prime $\ell\notin\{q,q'\}$ there are a global unit $s_1(\ell)\in H_2^\times$ and a finite idele $s_1^\flat(\ell)$ such that the components of $s_1^\flat(\ell)$ equal $s_1(\ell)\otimes 1$ at every place not containing $q'$ and $1$ at every place containing $q'$, such that the product of the diagonal idele of the scalar $\ell$ with $s_1^\flat(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` when $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise, and such that the reduced norm of $s_1(\ell)$ is $\ell$. A family $\Gamma_1$ of subgroups of $H_2^\times$ indexed by `HeckeTower.Obj q q'` $=\mathrm{Option}\{\ell\ \text{prime}:\ell\ne q,q'\}$ is given by: $\Gamma_1(\mathrm{none})$ consists of the units lying, at every finite place $w\ne v_1$, in the subgroup generated by the local box units of $R_2$ at $w$, and whose reduced norm has even $q'$-adic valuation; and $\Gamma_1(\ell)=\Gamma_1(\mathrm{none})\cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$. Elements $w_1,\bar w_1$ indexed by the same type satisfy: $w_1(\mathrm{none})$ lies in the away-from-$v_1$ unit group of $R_2$ and has reduced norm $q'$, and $w_1(\ell)$ lies in the away-from-$v_1$ unit group of `meetOrder R₂ (sf₁ ℓ)` with reduced norm $q'$; while $\bar w_1(\mathrm{none})$ has reduced norm $q$, its local image lies in the local box units of $R_2$ at every $u\ne v_1$ not containing $q$, and conjugation by it preserves, as an equivalence, the local box of $R_2$ and the local box of $\Lambda_2$ at every $u\ne v_1$; the same three conditions hold for $\bar w_1(\ell)$ with `meetOrder R₂ (sf₁ ℓ)` in place of $R_2$. Finally $\mathrm{dIso}_1$ is a homomorphism from the decomposition subgroup of $A_1$ over $\mathbb Q$ to the isometric automorphisms of the completion over $K_1$, whose underlying ring isomorphism is the Galois action.
--
--   The corresponding data at $A_2$ (for $H_1$, residue characteristic $q$), with the roles of $q$ and $q'$ interchanged throughout: $v_2$ containing $q$; $\iota_2,\rho_2,\varpi_2$ with $\varpi_2$ mapping to $q$ and `Omega.HolRingOf ϖ₂ ρ₂` a domain; $s_2,s_2^\flat$ with components $s_2(\ell)\otimes1$ away from $q$ and $1$ above $q$, dual condition relative to `meetOrder R₁ n₁`, and reduced norm $\ell$; $\Gamma_2$ defined by the away-from-$v_2$ unit group of $R_1$ together with evenness of the $q$-adic valuation of the reduced norm, and $\Gamma_2(\ell)$ the intersection with the $s_2(\ell)$-conjugate; $w_2$ of reduced norm $q$ in the away-from-$v_2$ unit groups of $R_1$, respectively of `meetOrder R₁ (sf₂ ℓ)`; $\bar w_2$ of reduced norm $q'$ with the local box conditions relative to $R_1$, $\Lambda_1$ and `meetOrder R₁ (sf₂ ℓ)`; and $\mathrm{dIso}_2$ implementing the Galois action by isometries.
--
--   Conclusion. There exist a $\mathbb Z$-submodule $\Lambda$ of $B$ which is a maximal order containing $R$, a `ShimuraCurveModel` $M$ for the data $R$, $\iota$ and the level family $\ell\mapsto$ `levelHeckeUSet Λ R ℓ` if $\ell\mid N$ and `primeHeckeSet R ℓ` otherwise (so $M$ packages a curve $M.F$ over $\mathbb Q$ together with its base changes $M.\mathrm{Fbar}$ over $\overline{\mathbb Q}$ and $M.\mathrm{Fc}$ over $\mathbb C$, the semilinear Galois action $M.\mathrm{gal}$, the group $M.J$, Hecke operators and correspondences), and a sign function $\varepsilon:\mathrm{Primes}\to\mathbb Z^\times$ such that:
--
--   (i) $\varepsilon(\ell)=1$ for every prime $\ell\ne q,q'$;
--
--   (ii) for every prime $p$, $M$ has `GoodReductionOutside p (D * p)`: for every prime $\ell\nmid Dp$ and every valuation subring $B'$ of $\overline{\mathbb Q}$ over $\ell$, every element of the inertia subgroup of $B'$ acts trivially on the $p$-torsion of $M.J$, and for every Frobenius element $\sigma$ at $\ell$ for $B'$ and every $p$-torsion point $t$ one has $\sigma^2t-T_\ell(\sigma t)+\ell\,t=0$, where $T_\ell$ is the Hecke operator `M.heckeJ (heckeGen ℓ)`;
--
--   and there exists a tower $\mathbb T$ : `HeckeTower.TowerData q q' M.Fbar`, i.e. for each prime $\ell\ne q,q'$ a curve field $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$ together with two finite integral $\overline{\mathbb Q}$-algebra maps $\mathbb T.\varphi(\ell,i)$, $i\in\{0,1\}$, from $M.\mathrm{Fbar}$ to $\mathbb T.F(\ell)$, such that:
--
--   (iii) each $\mathbb T.\mathrm{objField}\ j$ (that is $M.\mathrm{Fbar}$ for $j=\mathrm{none}$ and $\mathbb T.F(\ell)$ otherwise) contains an element $x$ transcendental over $\overline{\mathbb Q}$ such that the field is finite over $\overline{\mathbb Q}(x)$;
--
--   and there exist semilinear Galois actions $\mathrm{galT}(\ell)$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $\mathbb T.F(\ell)$ and semilinear automorphisms $W(0),W(1)$ of $M.\mathrm{Fbar}$ and $WT(\ell,0),WT(\ell,1)$ of $\mathbb T.F(\ell)$ satisfying, in this order: $\mathrm{galT}(\ell,\sigma)$ has base automorphism $\sigma$; for every arrow $\alpha=(\ell,i)$, every $\sigma$ and every $x\in M.\mathrm{Fbar}$, $\mathrm{galT}(\ell,\sigma)\cdot\mathbb T.\varphi(\alpha)(x)=\mathbb T.\varphi(\alpha)(M.\mathrm{gal}(\sigma)\cdot x)$; each $W(i)$ and each $WT(\ell,i)$ has trivial base automorphism; $W(i)^2=1$, $W(0)W(1)=W(1)W(0)$ and each $W(i)$ commutes with every $M.\mathrm{gal}(\sigma)$; $WT(\ell,i)^2=1$, $WT(\ell,0)WT(\ell,1)=WT(\ell,1)WT(\ell,0)$ and each $WT(\ell,i)$ commutes with every $\mathrm{galT}(\ell,\sigma)$; for every arrow $\alpha=(\ell,i')$, every $i$ and every $x$, $WT(\ell,i)\cdot\mathbb T.\varphi(\alpha)(x)=\mathbb T.\varphi(\alpha)(W(i)\cdot x)$;
--
--   (iv) on $M.J$ the action of $W(0)$ equals $\varepsilon(q)$ times $M.\mathrm{heckePic0}\ q$ and the action of $W(1)$ equals $\varepsilon(q')$ times $M.\mathrm{heckePic0}\ q'$;
--
--   (v) for every arrow $\alpha$ the degree `finrankAlong` of $\mathbb T.\varphi(\alpha)$ equals `HeckeTower.arrowDegree N α`, namely $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise;
--
--   (vi) for every prime $\ell\ne q,q'$ and every divisor on $M.\mathrm{Fbar}$, the correspondence $M.\mathrm{corrBar}\ \ell$ coincides with the divisor correspondence obtained by pulling back along $\mathbb T.\varphi(\ell,0)$ and pushing forward along $\mathbb T.\varphi(\ell,1)$;
--
--   (vii) there exist a character $\chi_1$ of the decomposition subgroup of $A_1$ over $\mathbb Q$ with values in $\mathrm{Multiplicative}(\mathbb Z/2)$ and, for each object $j$ of the tower, a ring embedding $\iota_{M,1}(j)$ of $\mathbb T.\mathrm{objField}\ j$ into the fraction field of `Omega.HolRingOf ϖ₁ ρ₁`, such that `DescentIntertwining q' 1 0 A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁ M.Fbar 𝕋` holds for the restrictions of $M.\mathrm{gal}$ and of the $\mathrm{galT}(\ell)$ to that decomposition subgroup, together with $W$, $WT$, $\chi_1$ and $\iota_{M,1}$; among the conditions contained in this predicate are that $\chi_1$ be trivial on the inertia subgroup of $A_1$, non-trivial on every Frobenius element at $q'$, and equal to $1$ exactly on those $\tau$ fixing all elements of the residue field of $A_1$ satisfying $x^{q'^2}=x$, and that each $\iota_{M,1}(j)$ restrict on $\overline{\mathbb Q}$ to the canonical map into the completion of $A_1$, the remaining conditions expressing the compatibility of the embeddings with $\Gamma_1$, $w_1$, $\bar w_1$, $s_1$, $\mathrm{dIso}_1$, the Galois actions and the two involutions, the indices $1$ and $0$ selecting which involution plays the role of the Atkin–Lehner element at $q'$ and at $q$;
--
--   (viii) the mirror assertion at $A_2$: there exist $\chi_2$ and embeddings $\iota_{M,2}(j)$ into the fraction field of `Omega.HolRingOf ϖ₂ ρ₂` such that `DescentIntertwining q 0 1 A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂ M.Fbar 𝕋` holds for the same restricted Galois actions, $W$, $WT$, $\chi_2$ and $\iota_{M,2}$.
--
--   The same sign function $\varepsilon$, model $M$, tower $\mathbb T$ and involutions $W,WT$ serve both (vii) and (viii); no uniqueness is asserted.
--
--   This is the Čerednik–Drinfeld uniformisation input, in descent form, for the Shimura curve $X^{qq'}_0(N)$ attached to the indefinite quaternion algebra of discriminant $qq'$: it produces the canonical rational model with its Eichler–Shimura relations outside $Dp$, its Hecke tower of prime-to-$qq'$ level maps with the two Atkin–Lehner involutions, and, at each of the two ramified primes, the identification of the tower over the completion with the rigid-analytic quotient data coming from the definite quaternion algebra ramified at the other prime. It is assembled from the corresponding statement for the base curve together with the two descent-intertwining theorems at $A_1$ and $A_2$, and feeds the construction of the interchange data used in level raising.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_cerednikInterchange_pair_of_six_mul_dvd_of_neZero
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
        CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
          M.Fbar 𝕋 (M.gal.comp (A₁.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₁.decompositionSubgroup ℚ).subtype) W WT χ₁ ιM₁) ∧

      (∃ (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂)),
        CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
          M.Fbar 𝕋 (M.gal.comp (A₂.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₂.decompositionSubgroup ℚ).subtype) W WT χ₂ ιM₂) := by sorry
