-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_exists_equivariant_conorm_pic0_constantFieldExtension
-- name    : CerednikDrinfeld.ShimuraCurveModel.exists_equivariant_conorm_pic0_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/531ad05c-ec42-5a9e-8004-95d1b16964c6
-- title:
--   Conorm from the Shimura Jacobian into Pic⁰ over a completed algebraic closure
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $R$ of $\mathbb{H}[\mathbb{Q},a,b]$, a $\mathbb{Q}$-algebra map $\iota_R$ from $\mathbb{H}[\mathbb{Q},a,b]$ to $2\times 2$ real matrices, a family $\mathcal{S}$ indexed by $\mathbb{N}$ of sets of units of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$, and a model $M : \mathrm{ShimuraCurveModel}\ R\ \iota_R\ \mathcal{S}$, with geometric function field $\bar F = M.\mathrm{Fbar}$ over $\overline{\mathbb{Q}}$, semilinear Galois action $M.\mathrm{gal}$ and induced action $M.\mathrm{galJ}$ on $M.J$. Assume $\bar F$ is a one-variable function field over $\overline{\mathbb{Q}}$: some $x\in\bar F$ is transcendental over $\overline{\mathbb{Q}}$ with $\bar F$ finite-dimensional over $\overline{\mathbb{Q}}(x)$. Let $r$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $r$ a non-unit of $A$, and $C =$ the completion of $\overline{\mathbb{Q}}$ at the valuation of $A$. Let $F_C$ be a field, an algebra over $C$, over $\bar F$ and over $\overline{\mathbb{Q}}$ with both towers commuting, which is a curve over $C$ in the project's sense (principal divisors exist, all residue fields are finite over $C$, and $\Omega[F_C/C]$ is free of rank one), again a one-variable function field over $C$, and generated over $C$ by the image of $\bar F$. Let $\sigma\mapsto \mathrm{galFC}(\sigma)$ be a homomorphism from the decomposition subgroup of $A$ over $\mathbb{Q}$ to the group of pairs of ring automorphisms of $F_C$ and of $C$ compatible with the structure map, such that $\mathrm{galFC}(\sigma)$ acts on the image of $f\in\bar F$ as the image of $M.\mathrm{gal}(\sigma)\cdot f$. Then there is an additive homomorphism $\iota_T : M.J \to \mathrm{Pic}^0(F_C/C)$, where classes $\mathrm{Pic0.mk}\,D$ of degree-zero divisors of $\bar F/\overline{\mathbb{Q}}$ are elements of $M.J$, such that: (i) $\iota_T(\mathrm{Pic0.mk}\,D) = \mathrm{Pic0.mk}\,D'$ whenever the degree-zero divisor $D'$ of $F_C/C$ satisfies $D'(v') = D(v)$ for every place $v'$ of $F_C/C$ whose valuation subring contracts along $\bar F\to F_C$ to that of a place $v$ of $\bar F/\overline{\mathbb{Q}}$, and $D'(v') = 0$ for every $v'$ contracting to no such place; (ii) $\iota_T$ is injective; (iii) every element of $\mathrm{Pic}^0(F_C/C)$ of finite additive order lies in the range of $\iota_T$; and (iv) $\iota_T(M.\mathrm{galJ}(\sigma)\,c) = \mathrm{galFC}(\sigma)\cdot \iota_T(c)$ for all $\sigma$ in the decomposition subgroup and all $c\in M.J$, the action on $\mathrm{Pic}^0(F_C/C)$ being the one induced by the semilinear automorphism group.
--
--   This is the comparison layer between the Jacobian of a Shimura curve model over $\overline{\mathbb{Q}}$ and divisor classes over the completion of $\overline{\mathbb{Q}}$ at a place above $r$: base change of degree-zero divisor classes is injective, hits exactly the torsion, and is equivariant for the decomposition group. It is used in the construction of a Shimura curve model with good reduction together with an equivariant Čerednik–Drinfeld uniformisation of the local Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_exists_equivariant_conorm_pic0_constantFieldExtension.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_Valuation_CompletionAlgebra
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open AlgebraicCurve CerednikDrinfeld

theorem CerednikDrinfeld.ShimuraCurveModel.exists_equivariant_conorm_pic0_constantFieldExtension
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ιR : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R ιR 𝒮)
    (hfg : ∃ x : M.Fbar, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set M.Fbar)) M.Fbar)
    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [Algebra M.Fbar FC]
    [Algebra (AlgebraicClosure ℚ) FC] [IsScalarTower (AlgebraicClosure ℚ) A.valuation.Completion FC]
    [IsScalarTower (AlgebraicClosure ℚ) M.Fbar FC] [IsCurveOver A.valuation.Completion FC]
    (hfg' : ∃ x : FC, Transcendental A.valuation.Completion x ∧
      FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)
    (hgen : IntermediateField.adjoin A.valuation.Completion (Set.range (algebraMap M.Fbar FC)) = ⊤)
    (galFC : ↥(A.decompositionSubgroup ℚ) →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_ext : ∀ (σ : ↥(A.decompositionSubgroup ℚ)) (f : M.Fbar),
      galFC σ • algebraMap M.Fbar FC f =
        algebraMap M.Fbar FC (M.gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • f)) :
    ∃ ιT : M.J →+ Pic0 A.valuation.Completion FC,

      (∀ (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := M.Fbar))
          (D' : Divisor.degZero (K := A.valuation.Completion) (F := FC)),
        (∀ (v' : Place A.valuation.Completion FC) (v : Place (AlgebraicClosure ℚ) M.Fbar),
          v'.toValuationSubring.comap (algebraMap M.Fbar FC) = v.toValuationSubring →
            (D' : Divisor A.valuation.Completion FC) v' = (D : Divisor (AlgebraicClosure ℚ) M.Fbar) v) →
        (∀ v' : Place A.valuation.Completion FC,
          (∀ v : Place (AlgebraicClosure ℚ) M.Fbar,
            v'.toValuationSubring.comap (algebraMap M.Fbar FC) ≠ v.toValuationSubring) →
            (D' : Divisor A.valuation.Completion FC) v' = 0) →
        ιT (Pic0.mk D) = Pic0.mk D') ∧

      Function.Injective ιT ∧

      (∀ t : Pic0 A.valuation.Completion FC, IsOfFinAddOrder t → t ∈ ιT.range) ∧

      (∀ (σ : ↥(A.decompositionSubgroup ℚ)) (c : M.J),
        ιT (M.galJ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) c) =
          ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC)
            (Pic0 A.valuation.Completion FC)).comp galFC) σ (ιT c)) := by sorry
