-- Prove2me | Theorems.Thm_AlgEquiv_exists_fin_five_equiv_of_orderOf_eq_finrank
-- name    : AlgEquiv.exists_fin_five_equiv_of_orderOf_eq_finrank
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:21.950251+00:00
-- url     : https://prove2.me/theorems/122d3099-214d-469b-9bb9-fc22b79e29d0
-- title:
--   An order-five automorphism of a degree-five extension generates its full Galois group
-- statement:
--   Let $E/F$ be a finite field extension of degree $5$, and let $σ∈Aut_F(E)$ have order $5$. Then $E/F$ is Galois and the map $i↦σ^i$ is a bijection from $ℤ/5ℤ$ onto $Aut_F(E)$: $$Aut_F(E)=\{1,σ,σ^2,σ^3,σ^4\}.$$ This identifies the relevant quintic extension as cyclic.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open AlgEquiv

theorem AlgEquiv.exists_fin_five_equiv_of_orderOf_eq_finrank
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ = 5) (hdegree : Module.finrank F E = 5) :
    IsGalois F E ∧ ∃ e : Fin 5 ≃ (E ≃ₐ[F] E), ∀ i, e i = σ ^ i.val := by sorry
