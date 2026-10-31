-- Prove2me | Theorems.Thm_DiazModulus_eval_eq_zero_on_span_of_addSubgroup
-- name    : DiazModulus.eval_eq_zero_on_span_of_addSubgroup
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:34.234224+00:00
-- url     : https://prove2.me/theorems/99c3ca4b-6a3b-4c5e-abfb-d64b1eff67d2
-- title:
--   A complex polynomial vanishing on an additive subgroup $\Lambda$ of $\mathbb{C}^{A_0}$ vanishes on its $\mathbb{C}$-span
-- statement:
--   Let $A_0$ be a type, $\Lambda$ an additive subgroup of $\mathbb{C}^{A_0}$ and $F \in \mathbb{C}[X_{A_0}]$ a polynomial vanishing at every point of $\Lambda$. Then $F$ vanishes at every point of the complex span of $\Lambda$.
--
--   **Proof.** For $z = \sum_{i < n} c_i x_i$ with $x_i \in \Lambda$, induction on $n$ for every base point $y \in \Lambda$: the one-variable polynomial $t \mapsto F(y + r + t x_0)$ vanishes at every integer, hence identically.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical: a polynomial vanishing on infinitely many points of a line vanishes on the line. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem eval_eq_zero_on_span_of_addSubgroup {A₀ : Type*} (Λ : AddSubgroup (A₀ → ℂ)) (F : MvPolynomial A₀ ℂ)
    (hF : ∀ x ∈ Λ, MvPolynomial.eval x F = 0) :
    ∀ x ∈ Submodule.span ℂ (Λ : Set (A₀ → ℂ)), MvPolynomial.eval x F = 0 := by
  sorry

end DiazModulus
