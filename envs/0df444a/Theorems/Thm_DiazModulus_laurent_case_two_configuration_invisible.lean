-- Prove2me | Theorems.Thm_DiazModulus_laurent_case_two_configuration_invisible
-- name    : DiazModulus.laurent_case_two_configuration_invisible
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-10T20:24:23.212998+00:00
-- url     : https://prove2.me/theorems/7527a895-a765-4126-bd2b-4e5db48f206e
-- title:
--   For u ∉ Q̄, Q̄u⁻¹ + Q̄ + Q̄u + Q̄u³ + Q̄u⁴ is spanned by the products of (1, u) and (u⁻¹, 1, u³), and contains none of u², u⁻², 1/(u − b)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $V = \overline{\mathbb{Q}}u^{-1} + \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^3 + \overline{\mathbb{Q}}u^4$. Then $(1, u)$ and $(u^{-1}, 1, u^3)$ are free over $\overline{\mathbb{Q}}$, their six products span $V$, and $V$ contains none of $u^2$, $u^{-2}$ and $1/(u - b)$ ($b \in \overline{\mathbb{Q}}$ non-zero).
--
--   So $V$ carries a $2 \times 3$ configuration whose products fill the whole five-dimensional space (the second case of the classification, not a geometric progression), and no four-dimensional $H_0 + \overline{\mathbb{Q}}w \subseteq V$ is one of Theorem B's. $V$ is not stable under conjugation, so it says nothing at a candidate; it shows that the conjugation condition is needed in the conjecture that every such space is either visible to Theorem B or contains a progression.
--
--   **Proof.** Distinct powers of the transcendental $u$ are free, so $(1, u)$ and $(u^{-1}, 1, u^3)$ are free; the six products are $u^{-1}, 1, u^3, 1, u, u^4$. A membership of $u^2$, $u^{-2}$ or $1/(u - b)$ in the span of $u^{-1}, 1, u, u^3, u^4$ clears to a polynomial identity: for $u^2$ the coefficient of $X^3$ is $-1$, for $u^{-2}$ the constant term is $1$, and for $1/(u - b)$ the identity $u = (u - b)P(u)$ fails at $b \neq 0$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R9 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 10 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_case_two_configuration_invisible (u : ℂ) (hu : u ∉ Qbar) :
    LinearIndependent (↥Qbar) ![1, u] ∧ LinearIndependent (↥Qbar) ![u⁻¹, 1, u ^ 3] ∧
      Submodule.span Qbar (Set.range fun ij : Fin 2 × Fin 3 => ![1, u] ij.1 * ![u⁻¹, 1, u ^ 3] ij.2) = Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧
      u ^ 2 ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧ (u ^ 2)⁻¹ ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) := by
  sorry

end DiazModulus
