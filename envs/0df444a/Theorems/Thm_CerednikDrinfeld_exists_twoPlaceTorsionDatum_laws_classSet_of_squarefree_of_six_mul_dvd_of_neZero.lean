-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/a44c2306-52c5-5d79-9fae-e1f8aa18be20
-- title:
--   Two-place p-torsion datum from Čerednik–Drinfeld over class-set graphs
-- statement:
--   Let $p$ be a prime, $N\neq 0$ squarefree, and $q,q'$ primes with $q\nmid N$, $q'\nmid N$, $q'\neq q$, $q\neq p$, $q'\neq p$ and $q,q'\geq 5$; let $D\neq 0$ be divisible by $6Nqq'$. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ with $q'$ (respectively $q$) a nonunit of $A_1$ (respectively $A_2$). For $i=2$ (the datum attached to $q$) take $a_2,b_2\in\mathbb{Q}$ with $a_2<0$, $b_2<0$ such that $\mathbb{H}[\mathbb{Q},a_2,b_2]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring exactly at the height-one prime $v$ containing $q$; let $\Lambda_2$ be a maximal order (maximal among orders) and $R_2\leq\Lambda_2$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$ in the first. Let $n_2$ be a unit of $\mathbb{H}[\mathbb{Q},a_2,b_2]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ lying in `primeHeckeSet R₂ q'`, i.e. $n_2$ and $q'n_2^{-1}$ lie in the finite adelic box of $R_2$ while $n_2^{-1}$ and $q'^{-1}n_2$ do not; assume $\mathrm{meetOrder}(R_2,n_2)=R_2\cap n_2R_2n_2^{-1}$ is an Eichler order of level $Nq'$, is stable under conjugation by $n_2$, and that right translation by $n_2$ is an involution on the class set of the finite-idèle stabiliser of $\mathrm{meetOrder}(R_2,n_2)$, these class sets being finite; assume further `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, for primes $\ell\neq q'$ the two degeneracy maps intertwine edge and vertex Hecke operators, and the joint kernel of the degeneracy maps is stable under all edge Hecke operators. Symmetrically for $a_1,b_1$, $\Lambda_1$, $R_1$, $n_1$ with the roles of $q$ and $q'$ exchanged. Then there exists a two-place $p$-torsion datum $\mathcal{J}$ — a finite abelian group killed by $p$ with a ring homomorphism from the abstract Hecke algebra, a commuting action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ trivial on the inertia of some finite level, and toric subgroups identified with $\mathrm{Hom}$ of the ribbon kernels into $\mathbb{Z}/p$ together with specialisation maps from the $A_1$- and $A_2$-inertia invariants to the ribbon component groups — over the degeneracy and Hecke data of the two class-set graphs $\mathrm{ClassSet}(\mathrm{meetOrder}(R_i,n_i))\rightrightarrows\mathrm{ClassSet}(R_i)$ and the places $A_1,A_2$, such that $\mathcal{J}$ satisfies `Laws (D * p) q' q`: good reduction outside $Dp$ for its first constituent, and the local laws at $q'$ and at $q$ for its first and second constituents respectively.
--
--   This is the Čerednik–Drinfeld uniformisation input at both primes of the discriminant of the indefinite quaternion algebra, packaged as a two-place torsion datum on the $p$-torsion of the Jacobian of the Shimura curve of level $N$ and discriminant $qq'$, with the dual graphs of the two reductions expressed through quaternionic class sets rather than supersingular points. It feeds the subsequent construction of two-place torsion data from supersingular level data, and thence the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra ModularCurve
open CerednikDrinfeld

theorem CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero
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
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁) :
    ∃ 𝒥 : TwoPlaceTorsionDatum p
        (classSetDegeneracyData R₂ n₂) (classSetHeckeData N q' Λ₂ R₂ n₂)
        (classSetDegeneracyData R₁ n₁) (classSetHeckeData N q Λ₁ R₁ n₁) A₁ A₂,
      𝒥.Laws (D * p) q' q := by sorry
