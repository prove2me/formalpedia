-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_toricUniformization_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_toricUniformization_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8e18a47c-ec34-519f-b9b0-8b3967b3ebe2
-- title:
--   Shimura curve model with toric uniformisations at q and q'
-- statement:
--   Fix a prime $p$, a nonzero squarefree $N$, primes $q \ne q'$ with $q,q' \ge 5$, neither dividing $N$ and both distinct from $p$, and a nonzero $D$ with $6Nqq' \mid D$. Fix valuation subrings $A_1, A_2$ of an algebraic closure of $\mathbb{Q}$ with $q'$ (resp. $q$) a nonunit of $A_1$ (resp. $A_2$). Two definite data sets are assumed, symmetric in $q \leftrightarrow q'$: rationals $a_2 < 0$, $b_2 < 0$ such that $\mathbb{H}[\mathbb{Q},a_2,b_2]$ is a division algebra over the completion at a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ exactly when $q \in v$; a maximal order $\Lambda_2$ containing an Eichler order $R_2$ of level $N$ (an intersection of two maximal orders of relative index $N$); a finite-idelic unit $n_2 \in \mathrm{primeHeckeSet}\,R_2\,q'$; the meet order $R_2 \cap n_2 R_2 n_2^{-1}$ is Eichler of level $Nq'$ and is normalised by $n_2$; the shift by $n_2$ on the class set of its finite-idèle stabiliser is an involution; finiteness of the relevant class sets; and $\mathrm{ClassSetHeckeLaws}\,N\,q'\,\Lambda_2\,R_2\,n_2$, i.e. pairwise commutation of the edge and of the vertex Hecke matrices, equivariance of edge operators away from $q'$ with respect to both degeneracy pushforwards, and stability of the ribbon kernel. Symmetrically for $a_1,b_1,\Lambda_1,R_1,n_1$ with $q'$ and $q$ interchanged. On the indefinite side, rationals $a,b$ with $0 < a$ or $0 < b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is locally a division algebra exactly at the primes containing $q$ or $q'$, an Eichler order $R$ of level $N$, and an injective $\mathbb{Q}$-algebra map $\iota$ into $M_2(\mathbb{R})$. The conclusion asserts the existence of a maximal order $\Lambda \supseteq R$, a `ShimuraCurveModel` $M$ for $R$, $\iota$ with level sets $\ell \mapsto \mathrm{levelHeckeUSet}\,\Lambda\,R\,\ell$ for $\ell \mid N$ and $\mathrm{primeHeckeSet}\,R\,\ell$ otherwise, and signs $\varepsilon$ on primes with $\varepsilon_\ell = 1$ for $\ell \notin \{q,q'\}$, such that $M$ satisfies $\mathrm{GoodReductionOutside}\,p\,(Dp)$ (trivial inertia action and the Eichler–Shimura relation $\sigma^2 - T_\ell\sigma + \ell$ on the $p$-torsion of $M.J$ at primes $\ell \nmid Dp$) and such that the types $\mathrm{ToricUniformization}$ at $q'$ for the class-set degeneracy and Hecke data of $(R_2,n_2)$ with $A_1$, and at $q$ for those of $(R_1,n_1)$ with $A_2$, are both nonempty, taken for $M.J$ with the $\varepsilon$-twisted Hecke action $M.\mathrm{heckeJSigned}\,\varepsilon$ and the Galois action $M.\mathrm{galJ}$.
--
--   This is the Shimura-curve half of the Čerednik–Drinfeld input to level lowering: it produces, for an indefinite quaternion algebra ramified exactly at $\{q,q'\}$, a rational model of the Shimura curve of level $N$ whose Jacobian has good reduction away from $Dp$ and admits Mumford-type toric uniformisations at both $q$ and $q'$, matched with the class-set graphs of the two associated definite quaternion algebras. It feeds the assembly of the two-place torsion datum used in the class-set formulation of level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_toricUniformization_pair_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open ModularCurve

theorem CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_toricUniformization_pair_of_six_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hqp : q ≠ p) (hq'p : q' ≠ p)
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
      M.GoodReductionOutside p (D * p) ∧
      Nonempty (ToricUniformization p q' (classSetDegeneracyData R₂ n₂) (classSetHeckeData N q' Λ₂ R₂ n₂)
        A₁ hA₁ M.J (M.heckeJSigned ε) M.galJ) ∧
      Nonempty (ToricUniformization p q (classSetDegeneracyData R₁ n₁) (classSetHeckeData N q Λ₁ R₁ n₁)
        A₂ hA₂ M.J (M.heckeJSigned ε) M.galJ) := by sorry
