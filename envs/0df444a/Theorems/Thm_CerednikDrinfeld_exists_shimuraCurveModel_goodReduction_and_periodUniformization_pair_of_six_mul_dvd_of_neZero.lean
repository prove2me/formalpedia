-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/c5e61291-53e6-565a-baa1-e1d15325289d
-- title:
--   Shimura curve model with period uniformisation at both q,q'
-- statement:
--   Let $N\ge 1$ be squarefree, let $q\neq q'$ be primes with $q,q'\ge 5$, neither dividing $N$, and let $D\ge 1$ be a non-zero natural number divisible by $6Nqq'$. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ with $q'$, respectively $q$, a non-unit of $A_1$, respectively $A_2$. On the definite side, fix rationals $a_2,b_2<0$ such that $\mathbb{H}[\mathbb{Q},a_2,b_2]$ stays a division algebra over the completion at a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ exactly when $q\in v$, a maximal order $\Lambda_2$ and an order $R_2\le\Lambda_2$ that is Eichler of level $N$ (an intersection of two maximal orders of relative index $N$), and a finite-adelic unit $n_2$ in the prime Hecke set of $R_2$ at $q'$ such that $\mathrm{meetOrder}\,R_2\,n_2=R_2\cap n_2R_2n_2^{-1}$ is Eichler of level $Nq'$, is normalised by $n_2$, and has the double shift by $n_2$ acting trivially on its class set, together with the predicate `ClassSetHeckeLaws` $N\,q'\,\Lambda_2\,R_2\,n_2$: the edge Hecke matrices commute with one another, the vertex Hecke matrices commute with one another, the two degeneracy pushforwards intertwine edge and vertex Hecke operators at every prime other than $q'$, and the edge operators preserve the ribbon kernel. Symmetrically, data $a_1,b_1,\Lambda_1,R_1,n_1$ with the roles of $q$ and $q'$ exchanged. Finally let $a,b$ be rationals with $0<a$ or $0<b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is a division algebra over the completion at $v$ exactly when $q\in v$ or $q'\in v$, let $R$ be an Eichler order of level $N$ in it, and let $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map. Then there are a maximal order $\Lambda\supseteq R$, a `ShimuraCurveModel` $M$ for $R$, $\iota$ and the Hecke sets $\ell\mapsto\mathrm{levelHeckeUSet}\,\Lambda\,R\,\ell$ for $\ell\mid N$ and $\mathrm{primeHeckeSet}\,R\,\ell$ otherwise, and signs $\varepsilon:\mathrm{Primes}\to\mathbb{Z}^\times$ with $\varepsilon_\ell=1$ for $\ell\notin\{q,q'\}$, such that for every prime $p$ the model has good reduction outside $Dp$ in the sense that the $p$-torsion of $M.J$ is fixed by the inertia subgroup at every prime $\ell\nmid Dp$ and satisfies the Eichler–Shimura relation $\sigma^2-T_\ell\sigma+\ell=0$ there for the untwisted Hecke action, and such that both `Mumford.PeriodUniformization` types are non-empty: one at $q'$ over $A_1$ for the class-set degeneracy and Hecke data of $(R_2,n_2)$, one at $q$ over $A_2$ for those of $(R_1,n_1)$, in each case for the group $M.J$ with the sign-twisted Hecke action $M.\mathrm{heckeJSigned}\,\varepsilon$ and the Galois action $M.\mathrm{galJ}$.
--
--   This is the Čerednik–Drinfeld uniformisation step in the form used later in the argument: it produces simultaneously a rational model of the Shimura curve of discriminant $qq'$ and level $N$ with Eichler–Shimura relations, and Mumford period uniformisations of its Jacobian at both $q$ and $q'$, expressed through the class-set degeneracy graphs of the two auxiliary definite quaternion algebras. It is the input to the variant of the same existence statement in which the period uniformisations are replaced by purely toric uniformisation presentations at a prime $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open ModularCurve

theorem CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero
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
      Nonempty (Mumford.PeriodUniformization q' (classSetDegeneracyData R₂ n₂) (classSetHeckeData N q' Λ₂ R₂ n₂)
        A₁ hA₁ M.J (M.heckeJSigned ε) M.galJ) ∧
      Nonempty (Mumford.PeriodUniformization q (classSetDegeneracyData R₁ n₁) (classSetHeckeData N q Λ₁ R₁ n₁)
        A₂ hA₂ M.J (M.heckeJSigned ε) M.galJ) := by sorry
