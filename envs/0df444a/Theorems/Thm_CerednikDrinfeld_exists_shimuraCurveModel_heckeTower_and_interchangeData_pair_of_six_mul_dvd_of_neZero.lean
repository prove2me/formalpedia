-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_interchangeData_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_interchangeData_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8b3d3440-750b-59eb-b4b6-39d643aa3b97
-- title:
--   Shimura curve model, Hecke tower and Čerednik interchange pair
-- statement:
--   Throughout, $\overline{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`, and for a rational quaternion algebra $B$ the group $(B\otimes_{\mathbb{Q}}\mathbb{A}_f)^\times$ of finite ideles is written multiplicatively; `primeHeckeSet Λ ℓ` is the set of those finite ideles $h$ such that $h$ and $\ell h^{-1}$ lie in the finite adelic box of the order $\Lambda$ while $h^{-1}$ and $\ell^{-1}h$ do not, `levelHeckeUSet Λ O ℓ` is the subset of `primeHeckeSet O ℓ` consisting of those $h$ with $h O h^{-1}\neq O$ and $O\not\le h\Lambda h^{-1}$, `meetOrder R n` is $R\cap nRn^{-1}$, [`Submodule.finiteIdeleStabilizer Λ`](def/Submodule_FiniteAdeleBox.html#L26) is the stabiliser of the adelic box of $\Lambda$, and `ClassSet U` is the double coset space of $(B\otimes_{\mathbb{Q}}\mathbb{A}_f)^\times$ by the diagonal image of $B^\times$ on the left and $U$ on the right. An Eichler order of level $N$ (`IsEichlerOrder`) is an intersection of two maximal orders having relative index $N$ in the first.
--
--   **Numerical data.** A non-zero squarefree $N$, two primes $q\neq q'$ with $5\le q$, $5\le q'$, neither dividing $N$, and a non-zero natural number $D$ with $6Nqq'\mid D$. Two valuation subrings of $\overline{\mathbb{Q}}$ are fixed: $A_1$ with $q'$ a non-unit of $A_1$ (`LiesOverPrime q'`) and $A_2$ with $q$ a non-unit of $A_2$.
--
--   **Definite data ramified at $q$ (subscript $2$).** Rationals $a_2,b_2$ with `IsDefiniteRamifiedExactlyAt q`, that is $a_2<0$, $b_2<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a_2,b_2]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring precisely when $q\in v$. Submodules $\Lambda_2,R_2$ with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ and $R_2\le\Lambda_2$; a finite idele $n_2\in$ `primeHeckeSet R₂ q'`; the hypotheses `hS₂` (the order `meetOrder R₂ n₂` is Eichler of level $Nq'$), `hnorm₂` (conjugation by $n_2$ fixes `meetOrder R₂ n₂`), `hsq₂` (the shift $x\mapsto \overline{x\,n_2}$ on `ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂))` is an involution), finiteness of the class sets of `meetOrder R₂ n₂` and of $R_2$, and `hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂`, whose four clauses require: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, for every prime $\ell\neq q'$ both degeneracy pushforwards carry the edge Hecke operator to the vertex Hecke operator, and for every prime $\ell$ the edge Hecke operator preserves the joint kernel of the two degeneracy pushforwards.
--
--   **Definite data ramified at $q'$ (subscript $1$).** The mirror-image package: rationals $a_1,b_1$ with `IsDefiniteRamifiedExactlyAt q'`, a maximal order $\Lambda_1$ and an Eichler order $R_1$ of level $N$ with $R_1\le\Lambda_1$, a finite idele $n_1\in$ `primeHeckeSet R₁ q`, hypotheses `hS₁`, `hnorm₁`, `hsq₁` as above with $q$ in place of $q'$, finiteness of the two class sets, and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁`.
--
--   **Indefinite data.** Rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ the completion of $\mathbb{H}[\mathbb{Q},a,b]$ at $v$ is a division ring precisely when $q\in v$ or $q'\in v$; an Eichler order $R$ of level $N$ in $\mathbb{H}[\mathbb{Q},a,b]$; and an injective $\mathbb{Q}$-algebra map $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$.
--
--   **Conclusion.** There exist a maximal order $\Lambda$ with $R\le\Lambda$ and a `ShimuraCurveModel R ι 𝒮` $M$ for the level family $\mathcal{S}(\ell)=$ `levelHeckeUSet Λ R ℓ` when $\ell\mid N$ and $\mathcal{S}(\ell)=$ `primeHeckeSet R ℓ` otherwise, and a sign function $\varepsilon:\mathbb{P}\to\mathbb{Z}^\times$, such that the following hold.
--
--   (i) $\varepsilon(\ell)=1$ for every prime $\ell\notin\{q,q'\}$.
--
--   (ii) For every prime $p$, `M.GoodReductionOutside p (D * p)`: for every prime $\ell\nmid Dp$ and every valuation subring $B$ of $\overline{\mathbb{Q}}$ lying over $\ell$, every element of the inertia subgroup at $B$ acts trivially on the $p$-torsion of `M.J`, and for every Frobenius element $\sigma$ at $\ell$ for such a $B$ and every $t\in$ `M.J` with $p\cdot t=0$ one has $\sigma^2 t-T_\ell(\sigma t)+\ell\, t=0$, the Hecke operator acting through `M.heckeJ`.
--
--   (iii) There exist tower data $\mathbb{T}:$ `HeckeTower.TowerData q q' M.Fbar`, consisting of a field $\mathbb{T}.F(\ell)$ for every prime $\ell\notin\{q,q'\}$, each a curve over $\overline{\mathbb{Q}}$ and essentially of finite type over it, together with, for each arrow $\alpha=(\ell,i)$ with $i\in\{0,1\}$, a $\overline{\mathbb{Q}}$-algebra map $\mathbb{T}.\varphi_\alpha:M.\mathrm{Fbar}\to\mathbb{T}.F(\ell)$ that is finite and integral; and, attached to them:
--
--   • for every $j\in$ `HeckeTower.Obj q q'` (that is, $j$ is either the base or a prime $\ell\notin\{q,q'\}$) an element $x$ of $\mathbb{T}.\mathrm{objField}(j)$ (which is $M.\mathrm{Fbar}$ in the first case and $\mathbb{T}.F(\ell)$ in the second) that is transcendental over $\overline{\mathbb{Q}}$ and such that $\mathbb{T}.\mathrm{objField}(j)$ is finite-dimensional over $\overline{\mathbb{Q}}(x)$;
--
--   • homomorphisms $\mathrm{galT}_\ell:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},\mathbb{T}.F(\ell))$ for every prime $\ell\notin\{q,q'\}$, a pair $W:\mathrm{Fin}\,2\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},M.\mathrm{Fbar})$, and pairs $\mathrm{WT}_\ell:\mathrm{Fin}\,2\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},\mathbb{T}.F(\ell))$, subject to: the base automorphism of $\mathrm{galT}_\ell(\sigma)$ is $\sigma$ itself; $\mathrm{galT}_{\alpha_1}(\sigma)\cdot\mathbb{T}.\varphi_\alpha(x)=\mathbb{T}.\varphi_\alpha(M.\mathrm{gal}(\sigma)\cdot x)$ for all arrows $\alpha$, all $\sigma$ and all $x$; each $W_i$ and each $\mathrm{WT}_{\ell,i}$ is $\overline{\mathbb{Q}}$-linear (its base automorphism is the identity); $W_i^2=1$, $W_0W_1=W_1W_0$, and each $W_i$ commutes with $M.\mathrm{gal}(\sigma)$ for every $\sigma$; $\mathrm{WT}_{\ell,i}^2=1$, $\mathrm{WT}_{\ell,0}\mathrm{WT}_{\ell,1}=\mathrm{WT}_{\ell,1}\mathrm{WT}_{\ell,0}$, and $\mathrm{WT}_{\ell,i}$ commutes with $\mathrm{galT}_\ell(\sigma)$; and $\mathrm{WT}_{\alpha_1,i}\cdot\mathbb{T}.\varphi_\alpha(x)=\mathbb{T}.\varphi_\alpha(W_i\cdot x)$ for all arrows $\alpha$, all $i$ and all $x$;
--
--   • on the group `M.J`: $W_0\cdot c=\varepsilon(q)\,\cdot$ `M.heckePic0 q _ c` and $W_1\cdot c=\varepsilon(q')\,\cdot$ `M.heckePic0 q' _ c` for every $c$, the sign acting as an integer scalar;
--
--   • numerical and correspondence normalisations: for every arrow $\alpha=(\ell,i)$, `finrankAlong` of $\mathbb{T}.\varphi_\alpha$ equals `HeckeTower.arrowDegree N α`, namely $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise; and for every prime $\ell\notin\{q,q'\}$ and every divisor on $M.\mathrm{Fbar}$, the model's geometric correspondence `M.corrBar ℓ` agrees with `Divisor.correspondence` of $\mathbb{T}.\varphi_{(\ell,0)}$ and $\mathbb{T}.\varphi_{(\ell,1)}$, that is with pushforward along $\mathbb{T}.\varphi_{(\ell,1)}$ of pullback along $\mathbb{T}.\varphi_{(\ell,0)}$.
--
--   **Mumford-side data at $A_1$ (over $q'$), with the definite algebra $\mathbb{H}[\mathbb{Q},a_2,b_2]$.** There exist: the property that the decomposition group of $A_1$ over $\mathbb{Q}$ acts isometrically for the valuation of $A_1$; a height-one prime $v_1$ of $\mathcal{O}_{\mathbb{Q}}$; an injective $\mathbb{Q}$-algebra map $\iota_1:\mathbb{H}[\mathbb{Q},a_2,b_2]\to M_2(\mathrm{ratClosure}\,A_1)$, where $\mathrm{ratClosure}\,A_1$ is the topological closure of the prime subfield inside the completion of $\overline{\mathbb{Q}}$ at the valuation of $A_1$; a homomorphism $\rho_1:\mathbb{H}[\mathbb{Q},a_2,b_2]^\times\to \mathrm{PGL}_2(\mathrm{ratClosure}\,A_1)$; a pseudo-uniformizer $\varpi_1$ of $\mathrm{ratClosure}\,A_1$ in that completion; the property that the holomorphic ring `Omega.HolRingOf ϖ₁ ρ₁` is a domain; families $s_1,\ sf_1$ indexed by the primes $\ell\notin\{q,q'\}$ with values in $\mathbb{H}[\mathbb{Q},a_2,b_2]^\times$ and in the finite ideles respectively; subgroups $\Gamma_1(j)\le\mathbb{H}[\mathbb{Q},a_2,b_2]^\times$ and units $w_1(j),\bar w_1(j)$ indexed by $j\in$ `HeckeTower.Obj q q'`; a homomorphism $\mathrm{dIso}_1$ from the decomposition subgroup of $A_1$ to the isometric automorphisms of the completion; a character $\chi_1$ of that decomposition subgroup with values in $\mathbb{Z}/2$ written multiplicatively; and ring homomorphisms $\iota M_1(j):\mathbb{T}.\mathrm{objField}(j)\to\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi_1\,\rho_1)$; such that: $q'\in v_1$; $\iota_1$ is injective; $\rho_1$ is the projectivisation of $\iota_1$ on units; $\varpi_1.\varpi$ maps to $q'$ in the completion; for every prime $\ell\notin\{q,q'\}$ the idele $sf_1(\ell)$ has component $s_1(\ell)\otimes 1$ at every height-one prime $u$ with $q'\notin u$ and component $1$ at every $u$ with $q'\in u$, the product of the diagonal idele of the scalar $\ell$ with $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` when $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise, and the reduced norm of $s_1(\ell)$ is $\ell$; $\Gamma_1(\mathrm{base})$ consists exactly of those units lying in `CosetGraph.awayUnits R₂ v₁` (the intersection over all $w\neq v_1$ of the preimages of the group generated by the local unit box of $R_2$ at $w$) whose reduced norm has even $q'$-adic valuation; $\Gamma_1(\ell)=\Gamma_1(\mathrm{base})\cap s_1(\ell)\Gamma_1(\mathrm{base})s_1(\ell)^{-1}$; $w_1(\mathrm{base})$ lies in `CosetGraph.awayUnits R₂ v₁` and has reduced norm $q'$, and $w_1(\ell)$ lies in `CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; $\bar w_1(\mathrm{base})$ has reduced norm $q$, its local image lies in the local unit box of $R_2$ at every $u\neq v_1$ with $q\notin u$, and conjugation by it preserves, at every $u\neq v_1$, both the local box of $R_2$ and the local box of $\Lambda_2$ (as an equivalence for each local element), and the same three conditions hold for $\bar w_1(\ell)$ with $R_2$ replaced by `meetOrder R₂ (sf₁ ℓ)`; $\mathrm{dIso}_1(\tau)$ acts on the completion as $\tau$ does; and finally the predicate [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) holds at the parameters $q'$, $i=1$, $\bar i=0$, $A_1$, $\rho_1$, $\varpi_1$, $\Gamma_1$, $w_1$, $\bar w_1$, $s_1$, $\mathrm{dIso}_1$, the base field $M.\mathrm{Fbar}$, the tower $\mathbb{T}$, the restriction of $M.\mathrm{gal}$ and of the $\mathrm{galT}_\ell$ to the decomposition subgroup of $A_1$, $W$, $\mathrm{WT}$, $\chi_1$ and $\iota M_1$; this predicate requires, among further compatibilities, that $\chi_1$ is trivial on the inertia subgroup at $A_1$, non-trivial at every Frobenius element at $q'$, and trivial exactly on those $\tau$ fixing every element $x$ of the residue field of $A_1$ with $x^{q'^2}=x$, and that each $\iota M_1(j)$ restricts on $\overline{\mathbb{Q}}$ to the canonical map into the completion.
--
--   **Mumford-side data at $A_2$ (over $q$), with the definite algebra $\mathbb{H}[\mathbb{Q},a_1,b_1]$.** The same package with the roles of the two primes interchanged: $v_2$ contains $q$, $\varpi_2$ maps to $q$, the idele components of $sf_2(\ell)$ are $s_2(\ell)\otimes1$ away from $q$ and $1$ at $q$, the Hecke membership is in `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` or `primeHeckeSet (meetOrder R₁ n₁) ℓ` according as $\ell\mid N$ or not, $\Gamma_2(\mathrm{base})$ is cut out inside `CosetGraph.awayUnits R₁ v₂` by evenness of the $q$-adic valuation of the reduced norm, $w_2$ has reduced norm $q$ and $\bar w_2$ reduced norm $q'$ with the corresponding local box conditions for $R_1$, `meetOrder R₁ (sf₂ ℓ)` and $\Lambda_1$, $\mathrm{dIso}_2(\tau)$ acts as $\tau$, and [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) holds at the parameters $q$, $i=0$, $\bar i=1$, $A_2$, $\rho_2$, $\varpi_2$, $\Gamma_2$, $w_2$, $\bar w_2$, $s_2$, $\mathrm{dIso}_2$, $M.\mathrm{Fbar}$, $\mathbb{T}$, the restrictions of $M.\mathrm{gal}$ and of the $\mathrm{galT}_\ell$ to the decomposition subgroup of $A_2$, $W$, $\mathrm{WT}$, $\chi_2$ and $\iota M_2$.
--
--   This is the packaging statement for the Shimura curve $X_0^{qq'}(N)$ attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: it produces simultaneously a model with Eichler–Shimura good reduction outside $Dp$, the prime-to-$qq'$ Hecke tower with its two degeneracy maps and the two commuting Atkin–Lehner involutions acting on the Jacobian as $\pm T_q$ and $\pm T_{q'}$, and, at each of the two discriminant places, the Mumford-side presentation (arithmetic groups, norm-$q$ and norm-$q'$ units, pseudo-uniformizer and holomorphic ring) together with the Čerednik descent intertwining datum. It is the input to the equivariant $p$-adic uniformization form of the same package, which in turn feeds the level-lowering argument at the two primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_heckeTower_and_interchangeData_pair_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_shimuraCurveModel_heckeTower_and_interchangeData_pair_of_six_mul_dvd_of_neZero
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
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
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

      (∃ (hiso₁ : Fact (A₁.DecompositionIsometric ℚ))
         (v₁ : HeightOneSpectrum (𝓞 ℚ))
         (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))
         (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
         (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
         (hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁))
         (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
         (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
         (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
         (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
         (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
         (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁)),
        haveI := hiso₁
        haveI := hdom₁
        (((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal) ∧
        (Function.Injective ι₁) ∧
        (∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x)) ∧
        (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion)) ∧
        (∀ ℓ : HeckeTower.AwayPrime q q',
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
          nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ)) ∧
        (∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
          x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂])))) ∧
        (∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom) ∧
        ((w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
          ∀ ℓ : HeckeTower.AwayPrime q q',
          w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
        ((nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
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
          x ∈ Submodule.localBox Λ₂ u)))) ∧
        (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x) ∧
        CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
          M.Fbar 𝕋 (M.gal.comp (A₁.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₁.decompositionSubgroup ℚ).subtype) W WT χ₁ ιM₁) ∧

      (∃ (hiso₂ : Fact (A₂.DecompositionIsometric ℚ))
         (v₂ : HeightOneSpectrum (𝓞 ℚ))
         (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂))
         (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
         (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
         (hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂))
         (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
         (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
         (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
         (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
         (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
         (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂)),
        haveI := hiso₂
        haveI := hdom₂
        (((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal) ∧
        (Function.Injective ι₂) ∧
        (∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x)) ∧
        (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧
        (∀ ℓ : HeckeTower.AwayPrime q q',
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
          nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ)) ∧
        (∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
          x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁])))) ∧
        (∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom) ∧
        ((w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
          ∀ ℓ : HeckeTower.AwayPrime q q',
          w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
        ((nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
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
          x ∈ Submodule.localBox Λ₁ u)))) ∧
        (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x) ∧
        CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
          M.Fbar 𝕋 (M.gal.comp (A₂.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₂.decompositionSubgroup ℚ).subtype) W WT χ₂ ιM₂) := by sorry
