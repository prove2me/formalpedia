-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_sum_galois_smul_eq_zero_of_subsingleton
-- name    : AlgebraicCurve.Pic0.sum_galois_smul_eq_zero_of_subsingleton
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:33.208202+00:00
-- url     : https://prove2.me/theorems/b94c3d66-e90d-447b-992b-45144e507b81
-- title:
--   The Galois trace of a degree-zero divisor class vanishes over a trivial base $Pic^0$
-- statement:
--   Let $K⊆F⊆E$ be a scalar tower of fields with $E/F$ finite Galois. Assume principal divisors exist for $E/K$ and $Pic^0(K,F)$ is trivial. Then every $x∈Pic^0(K,E)$ satisfies $$\sum_{σ∈Gal(E/F)}σ·x=0,$$ where each $σ$ is restricted to a $K$-semilinear automorphism. This is the general divisor-class trace identity behind the cyclic order-five case.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward

set_option autoImplicit false
open AlgebraicCurve
open AlgebraicCurve.Pic0

theorem AlgebraicCurve.Pic0.sum_galois_smul_eq_zero_of_subsingleton
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] [Subsingleton (Pic0 K F)] (x : Pic0 K E) :
    ∑ σ : E ≃ₐ[F] E, SemilinearAut.ofAlgAut (σ.restrictScalars K) • x = 0 := by sorry
