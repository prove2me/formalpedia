-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor1_PQ
-- name    : DiazModulus.diaz_2007_cor1_PQ
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:22.105361+00:00
-- url     : https://prove2.me/theorems/4fe9fcb6-0600-4b64-8a7d-efa293b739a9
-- title:
--   Diaz 2007, Corollaire 1 (PQ): products and quotients outside ℒ̃, under the strong six exponentials theorem
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   1. Let $\lambda_0, \lambda_1, \lambda_2 \in \widetilde{\mathcal{L}}$ with $(\lambda_0, \lambda_2, \bar\lambda_2)$ linearly independent over $\overline{\mathbb{Q}}$ and $\lambda_1/\lambda_0 \in (\mathbb{R} \cup i\mathbb{R}) \setminus \overline{\mathbb{Q}}$. Then $\lambda_1\lambda_2/\lambda_0 \notin \widetilde{\mathcal{L}}$.
--   2. Let $\lambda_1, \lambda_2 \in \widetilde{\mathcal{L}}$ with $(\lambda_1, \lambda_2, \lambda_1\lambda_2)$ linearly independent. Then $\lambda_1\lambda_2$ and $\lambda_1/\lambda_2$ are not both in $\widetilde{\mathcal{L}}$.
--   3. Let $\lambda_1, \lambda_2 \in \widetilde{\mathcal{L}}$ with $\lambda_2 \neq 0$ and $(1, \lambda_1, 1/\lambda_2)$ linearly independent. Then $\lambda_1\lambda_2$ and $1/\lambda_2$ are not both in $\widetilde{\mathcal{L}}$. In particular, for $\lambda \in \widetilde{\mathcal{L}} \setminus \overline{\mathbb{Q}}$, $\lambda^2$ and $1/\lambda$ are not both in $\widetilde{\mathcal{L}}$.
--   4. Let $\lambda_0, \lambda_1 \in \widetilde{\mathcal{L}}$ with $(\lambda_0^2, \lambda_1, \lambda_0\lambda_1)$ linearly independent. Then $\lambda_1/\lambda_0$ and $\lambda_1/\lambda_0^2$ are not both in $\widetilde{\mathcal{L}}$. In particular, for $\lambda \in \widetilde{\mathcal{L}} \setminus \overline{\mathbb{Q}}$, $1/\lambda$ and $1/\lambda^2$ are not both in $\widetilde{\mathcal{L}}$.
--
--   **Proof.** Each part is the quotient form of the theorem (`DiazModulus.strong_six_exponentials_iff_quotient_form`) applied to one family, as in Diaz's proof: $(\lambda_0, \lambda_1, \lambda_2, \bar\lambda_2)$, $(\lambda_1\lambda_2, \lambda_1, \lambda_2, \lambda_1)$, $(1/\lambda_2, 1, \lambda_1, 1)$ and $(1, \lambda_0, \lambda_1/\lambda_0, \lambda_1/\lambda_0^2)$. In part 1 the second number $\lambda_1\bar\lambda_2/\lambda_0$ is $\pm$ the conjugate of the first.
--
--   **Novelty.** None: this is Corollaire 1 (PQ) of Diaz (2007), pp. 379–380, with his proof (p. 381). Part 1 relaxes the hypotheses of Corollary 2.9 of Waldschmidt's *Variations*. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 1 (PQ), pp. 379–380, proof p. 381. Part 1 relaxes the hypotheses of M. Waldschmidt, Variations on the six exponentials theorem, in: Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Corollary 2.9. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 1 (PQ)**, parts 1)–4) with the two "in particular" clauses, under Roy's strong six
exponentials theorem `hSSE`. -/
theorem diaz_2007_cor1_PQ
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ l₀ l₁ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∉ Qbar →
      l₁ * l₂ / l₀ ∉ LogAlgTilde) ∧
    -- 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₁ + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ l₁ / l₂ ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₂ ≠ 0 →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₁ + c * (1 / l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ 1 / l₂ ∈ LogAlgTilde)) ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → ¬ (l ^ 2 ∈ LogAlgTilde ∧ 1 / l ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ ^ 2 + b * l₁ + c * (l₀ * l₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ / l₀ ∈ LogAlgTilde ∧ l₁ / l₀ ^ 2 ∈ LogAlgTilde)) ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar →
      ¬ (1 / l ∈ LogAlgTilde ∧ 1 / l ^ 2 ∈ LogAlgTilde)) := by
  sorry

end DiazModulus
