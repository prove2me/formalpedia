-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_th4
-- name    : DiazModulus.diaz_2007_th4
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:43.326278+00:00
-- url     : https://prove2.me/theorems/01a3376c-0c8d-4711-a564-9e19cd8d4fef
-- title:
--   Diaz 2007, Théorème 4: x₂/x₁ ∈ ℒ̃ keeps the four products out of ℒ̃ (strong six exponentials) and out of ℒ (with Baker)
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   1. Let $x_1, x_2$ be linearly independent over $\overline{\mathbb{Q}}$ and $(y_1, y_2, 1/x_1)$ linearly independent over $\overline{\mathbb{Q}}$. If $x_2/x_1 \in \widetilde{\mathcal{L}}$, the four numbers $x_1y_1, x_1y_2, x_2y_1, x_2y_2$ are not all in $\widetilde{\mathcal{L}}$.
--   2. Let $x_1, x_2$ be linearly independent over $\mathbb{Q}$ and $y_1, y_2$ linearly independent over $\mathbb{Q}$. If $x_2/x_1 \in \widetilde{\mathcal{L}}$, the four numbers are not all in $\mathcal{L}$.
--
--   **Proof.** Part 1 is the theorem applied to $(x_1, x_2)$ and $(y_1, y_2, 1/x_1)$, whose two extra products are $1$ and $x_2/x_1$. For part 2, if the four numbers are logarithms, Baker's theorem makes $(x_1, x_2)$ and $(1/x_1, y_1, y_2)$ independent over $\overline{\mathbb{Q}}$, and part 1 applies.
--
--   **Novelty.** None: this is Théorème 4 of Diaz (2007), p. 385, with his proof (p. 386). Diaz presents it as a corollary of the strong six exponentials theorem that generalises Waldschmidt's five exponentials theorem. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 4, p. 385, proof p. 386. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Théorème 4**, parts 1) and 2), under Roy's strong six exponentials theorem `hSSE`; part 2)
also uses Baker's theorem `hB`. -/
theorem diaz_2007_th4
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ x₁ x₂ y₁ y₂ : ℂ,
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x₁ + b * x₂ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * y₁ + b * y₂ + c * (1 / x₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      x₂ / x₁ ∈ LogAlgTilde →
      ¬ (x₁ * y₁ ∈ LogAlgTilde ∧ x₁ * y₂ ∈ LogAlgTilde ∧ x₂ * y₁ ∈ LogAlgTilde ∧ x₂ * y₂ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ x₁ x₂ y₁ y₂ : ℂ,
      (∀ p q : ℚ, (p : ℂ) * x₁ + (q : ℂ) * x₂ = 0 → p = 0 ∧ q = 0) →
      (∀ p q : ℚ, (p : ℂ) * y₁ + (q : ℂ) * y₂ = 0 → p = 0 ∧ q = 0) →
      x₂ / x₁ ∈ LogAlgTilde →
      ¬ (x₁ * y₁ ∈ LogAlg ∧ x₁ * y₂ ∈ LogAlg ∧ x₂ * y₁ ∈ LogAlg ∧ x₂ * y₂ ∈ LogAlg)) := by
  sorry

end DiazModulus
