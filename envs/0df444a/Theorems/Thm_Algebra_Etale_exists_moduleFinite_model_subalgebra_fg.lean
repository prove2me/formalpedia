-- Prove2me | Theorems.Thm_Algebra_Etale_exists_moduleFinite_model_subalgebra_fg
-- name    : Algebra.Etale.exists_moduleFinite_model_subalgebra_fg
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T17:23:24.489344+00:00
-- url     : https://prove2.me/theorems/a5cf614d-2d4b-4198-9f79-c59937e86311
-- title:
--   Descent of a finite étale algebra to a finitely generated coefficient subalgebra
-- statement:
--   Let $A$ be a commutative $R$-algebra and $B$ a finite étale $A$-algebra. There is a finitely generated $R$-subalgebra $A_0\subseteq A$ and a finite étale $A_0$-algebra $B_0$ such that $A\otimes_{A_0}B_0\cong B$ as $A$-algebras.
-- source:
--   Stacks Project, Lemma 10.143.3 (8), https://stacks.math.columbia.edu/tag/00U2, and Lemma 32.8.3 on descent of finite morphisms.

import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

set_option autoImplicit false
open scoped TensorProduct
universe u

theorem Algebra.Etale.exists_moduleFinite_model_subalgebra_fg
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra.Etale A B] [Module.Finite A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Algebra.Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧ Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by sorry
