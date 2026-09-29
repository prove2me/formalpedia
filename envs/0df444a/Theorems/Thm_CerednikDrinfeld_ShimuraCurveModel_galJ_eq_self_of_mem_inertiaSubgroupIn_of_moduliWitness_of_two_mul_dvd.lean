-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd
-- name    : CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/1fa82de8-22bb-5ac9-b4cf-3026e3f27e02
-- title:
--   Inertia fixes p-torsion of the Shimura curve Jacobian
-- statement:
--   Fix natural numbers $N$ (nonzero and squarefree) and primes $q,q'$ with $q'\neq q$, $q\nmid N$, $q'\nmid N$ and $q,q'\geq 5$, and a natural number $D$ divisible by $2Nqq'$. Let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q\in v$ or $q'\in v$. Let $R$ be an Eichler order of level $N$ (an intersection of two maximal orders with relative index $N$), $\iota$ an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$, and $\Lambda$ a maximal order containing $R$. Let $M$ be a `ShimuraCurveModel` for $R$, $\iota$ and the Hecke data given by `levelHeckeUSet Λ R ℓ` at primes $\ell\mid N$ and `primeHeckeSet R ℓ` elsewhere. Assume: a witness $w$ of type `M.ModuliWitnessD Λ N q q' D` (a smooth proper integral scheme over $\mathbb{Z}[1/D]$ with a fake-elliptic-curve moduli interpretation, an identification of $M.F$ with its function field, and a bijection of places of $M.\mathrm{Fbar}$ with geometric points) which is a good reduction model, i.e. $\pi_X$ is smooth of relative dimension $1$ and all its geometric fibres over $\mathbb{Z}[1/D]$ are integral; a hypothesis lifting fake elliptic curves over $\overline{\mathbb{Q}}$ to valuation subrings in which $Nqq'$ is invertible; signs $\varepsilon$ equal to $1$ away from $q,q'$; a Hecke tower $\mathbb{T}$ of function fields indexed by primes $\ell\notin\{q,q'\}$, each carrying two finite integral $\overline{\mathbb{Q}}$-algebra maps from $M.\mathrm{Fbar}$, with semilinear Galois actions `galT`, involutions $W$ on $M.\mathrm{Fbar}$ and $WT$ on the tower fields, and the compatibilities (semilinearity over the base, $W$-squares trivial, commutations with each other and with Galois, intertwining along the tower maps, the action of $W_0,W_1$ on $M.J$ given by $\varepsilon$ times `heckePic0` at $q$, resp. $q'$, the action on point divisors, the degrees $\ell$ or $\ell+1$ according to $\ell\mid N$, and the identification of `corrBar ℓ` with the divisor correspondence of the two tower maps), all summarised here. Then for every prime $p$, every prime $\ell$ with $\ell\nmid Dp$, every valuation subring $B$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $B$, every $\sigma$ in the inertia subgroup of $B$ over $\mathbb{Q}$, and every $t\in M.J$ with $p\,t=0$, one has $M.\mathrm{galJ}\,\sigma\,t=t$.
--
--   This is the unramifiedness half of the good-reduction statement for the Jacobian of the Shimura curve attached to an Eichler order of level $N$ in the indefinite quaternion algebra ramified exactly at $q,q'$: the $p$-torsion of $J=\operatorname{Pic}^0$ is fixed by inertia at every prime $\ell$ not dividing $Dp$. It feeds the assembly of the good-reduction-outside-$Dp$ conclusion for the Shimura curve model together with its Hecke tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_moduliWitness_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ))
    (w : M.ModuliWitnessD Λ N q q' D) (hgood : w.IsGoodReductionModel)

    (hlift : ∀ (B : ValuationSubring (AlgebraicClosure ℚ)), IsUnit (((N * q * q' : ℕ) : ℤ) : ↥B) →
      ∀ E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ), ∃ 𝒜 : CerednikDrinfeld.QM.FakeEllipticCurve Λ N ↥B,
        CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback (B.subtype : ↥B →+* AlgebraicClosure ℚ) 𝒜 E)
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
    (hhecke : ∀ (ℓ : HeckeTower.AwayPrime q q') (Dv : Divisor (AlgebraicClosure ℚ) M.Fbar),
      M.corrBar ℓ.1 ℓ.1.prop Dv = Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) Dv)
    :
    ∀ p : ℕ, p.Prime → ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ D * p →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : M.J, p • t = 0 → M.galJ σ t = t := by sorry
