-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor4
-- name    : DiazModulus.diaz_2007_cor4
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:35.797987+00:00
-- url     : https://prove2.me/theorems/7fc3b619-9f71-4f27-9e62-387ecfa7dce2
-- title:
--   Diaz 2007, Corollaire 4: pairs of quotients outside ℒ̃, under the strong six exponentials theorem
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   1. Let $\lambda_1, \lambda_2, \lambda_3, \lambda_4 \in \widetilde{\mathcal{L}}$ with $(\lambda_1\lambda_2, \lambda_1\lambda_4, \lambda_2\lambda_3)$ and $(\lambda_1, \lambda_2)$ linearly independent over $\overline{\mathbb{Q}}$. Then $\lambda_4\lambda_1/\lambda_2$ and $\lambda_3\lambda_2/\lambda_1$ are not both in $\widetilde{\mathcal{L}}$.
--   2. If $(\lambda_1, \lambda_2, \lambda_1\lambda_2)$ is linearly independent, $\lambda_1/\lambda_2$ and $\lambda_2/\lambda_1$ are not both in $\widetilde{\mathcal{L}}$.
--   3. If $(\lambda_1, \lambda_2)$ is linearly independent, $\lambda_1^2/\lambda_2$ and $\lambda_2^2/\lambda_1$ are not both in $\widetilde{\mathcal{L}}$.
--   4. Let $\lambda_1, \lambda_3 \in \widetilde{\mathcal{L}}$ with $(\lambda_1, \bar\lambda_1)$ and $(\lambda_1\bar\lambda_1, \lambda_1\bar\lambda_3, \bar\lambda_1\lambda_3)$ linearly independent. Then $\lambda_1\bar\lambda_3/\bar\lambda_1 \notin \widetilde{\mathcal{L}}$.
--
--   Part 3 is the $\widetilde{\mathcal{L}}$ form of `DiazModulus.log_square_duality`, and part 4 that of `DiazModulus.conj_ratio_multiplier_relation` (with $\lambda_1 = u$, $\lambda_3 = \bar w$).
--
--   **Proof.** Part 1 is the theorem applied to $x = (\lambda_1, \lambda_2)$ and $y = (1, \lambda_3/\lambda_1, \lambda_4/\lambda_2)$. Parts 2, 3 and 4 are part 1 at $\lambda_3 = \lambda_4 = 1$, at $(\lambda_3, \lambda_4) = (\lambda_2, \lambda_1)$, and at $(\lambda_2, \lambda_4) = (\bar\lambda_1, \bar\lambda_3)$; in part 4 the two numbers are conjugate.
--
--   **Novelty.** None: this is Corollaire 4 of Diaz (2007), p. 383, with his proof (pp. 383–384). The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 4, p. 383, proof pp. 383–384. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 4**, parts 1)–4), under Roy's strong six exponentials theorem `hSSE`. -/
theorem diaz_2007_cor4
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ l₁ l₂ l₃ l₄ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde →
      l₄ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * (l₁ * l₂) + b * (l₁ * l₄) + c * (l₂ * l₃) = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * l₂ = 0 → a = 0 ∧ b = 0) →
      ¬ (l₄ * l₁ / l₂ ∈ LogAlgTilde ∧ l₃ * l₂ / l₁ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₁ + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ / l₂ ∈ LogAlgTilde ∧ l₂ / l₁ ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * l₂ = 0 → a = 0 ∧ b = 0) →
      ¬ (l₁ ^ 2 / l₂ ∈ LogAlgTilde ∧ l₂ ^ 2 / l₁ ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l₁ l₃ : ℂ, l₁ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * conj l₁ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * (l₁ * conj l₁) + b * (l₁ * conj l₃) + c * (conj l₁ * l₃) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l₁ * conj l₃ / conj l₁ ∉ LogAlgTilde) := by
  sorry

end DiazModulus
