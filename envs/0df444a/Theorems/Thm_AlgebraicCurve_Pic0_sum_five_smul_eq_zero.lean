-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_sum_five_smul_eq_zero
-- name    : AlgebraicCurve.Pic0.sum_five_smul_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:45.770016+00:00
-- url     : https://prove2.me/theorems/89f73291-c49f-4e6c-9dfb-dd0cb99af429
-- title:
--   The orbit sum under a cyclic degree-five automorphism vanishes in $Pic^0$
-- statement:
--   Let $F_0⊆F⊆L$ be intermediate fields over $K$. Assume principal divisors exist for $F/K$, $Pic^0(K,F_0)$ is trivial, $[F:F_0]=5$, and $g∈Aut_K(F)$ has order $5$ and fixes $F_0$ pointwise. Then for every $x∈Pic^0(K,F)$, $$\sum_{i=0}^{4}g^i·x=0.$$ This trace relation controls the order-five action on divisor classes.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward

set_option autoImplicit false
open AlgebraicCurve
open AlgebraicCurve.Pic0

theorem AlgebraicCurve.Pic0.sum_five_smul_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F₀ F : IntermediateField K L) (hle : F₀ ≤ F)
    [HasPrincipalDivisors K F] [Subsingleton (Pic0 K F₀)]
    (g : F ≃ₐ[K] F) (horder : orderOf g = 5)
    (hdegree : F₀.relfinrank F = 5)
    (hfix : ∀ a : F₀, g ⟨a.val, hle a.property⟩ = ⟨a.val, hle a.property⟩)
    (x : Pic0 K F) :
    ∑ i : Fin 5, SemilinearAut.ofAlgAut (g ^ i.val) • x = 0 := by sorry
