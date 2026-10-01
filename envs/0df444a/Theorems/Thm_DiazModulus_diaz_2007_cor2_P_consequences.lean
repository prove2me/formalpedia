-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor2_P_consequences
-- name    : DiazModulus.diaz_2007_cor2_P_consequences
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:00.340459+00:00
-- url     : https://prove2.me/theorems/c8926905-c0d4-4e72-8479-a2ce4e6c3aed
-- title:
--   Diaz 2007, Corollaire 2 (P) 2) and its Conséquences 1–3, under the strong six exponentials theorem
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   - **Corollaire 2 (P) 2).** Let $\lambda_1, \lambda_2 \in \widetilde{\mathcal{L}}$ with $\lambda_1 \in (\mathbb{R} \cup i\mathbb{R}) \setminus \overline{\mathbb{Q}}$ and $(1, \lambda_2, \bar\lambda_2)$ linearly independent over $\overline{\mathbb{Q}}$. Then $\lambda_1\lambda_2 \notin \widetilde{\mathcal{L}}$.
--   - **Conséquence 1.** For $\lambda \in \widetilde{\mathcal{L}}$ with $(1, \lambda, \bar\lambda)$ linearly independent, $\lambda^2$ and $|\lambda|^2$ are not both in $\widetilde{\mathcal{L}}$.
--   - **Conséquence 2.** For $\lambda_1, \lambda_2 \in \widetilde{\mathcal{L}}$ with $(1, \lambda_2, \lambda_1\lambda_2)$ linearly independent, $\lambda_1\lambda_2$ and $\lambda_1^2\lambda_2$ are not both in $\widetilde{\mathcal{L}}$.
--   - **Conséquence 3.** For $\lambda \in \widetilde{\mathcal{L}} \setminus \overline{\mathbb{Q}}$, $\lambda^2$ and $\lambda^3$ are not both in $\widetilde{\mathcal{L}}$.
--
--   At $\lambda = i\pi$, Conséquence 3 says that $e^{\alpha\pi^2}$ or $e^{\beta\pi^3}$ is transcendental for all non-zero algebraic $\alpha, \beta$ (`DiazModulus.pi_powers_not_both_mem_logAlgTilde`).
--
--   **Proof.** Corollaire 2 (P) 2) is part 1 of `DiazModulus.diaz_2007_cor1_PQ` at $\lambda_0 = 1$. The Conséquences apply Corollaire 2 (P) 1), already formalised as `Diaz.diaz_2007_cor2_P1`, to $(\lambda, \lambda, \bar\lambda)$ and to $(\lambda_1, \lambda_2, \lambda_1\lambda_2)$; the hypothesis of that node is supplied by `DiazModulus.strong_six_exponentials_iff_quotient_form`. Conséquence 3 is Conséquence 2 at $\lambda_1 = \lambda_2 = \lambda$.
--
--   **Novelty.** None: these are Diaz (2007), p. 381. Corollaire 2 (P) 2) is also Corollary 2.7 of Waldschmidt's *Variations*, credited there to Diaz. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 2 (P) 2) and Conséquences 1–3 of Corollaire 2 (P), p. 381. Corollaire 2 (P) 2) is also M. Waldschmidt, Variations on the six exponentials theorem, in: Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Corollary 2.7 (G. Diaz). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 2 (P) 2) and the Conséquences 1)–3) of Corollaire 2 (P)**, under Roy's strong six
exponentials theorem `hSSE`. -/
theorem diaz_2007_cor2_P_consequences
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- Corollaire 2 (P), 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (l₁.im = 0 ∨ l₁.re = 0) → l₁ ∉ Qbar →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l₁ * l₂ ∉ LogAlgTilde) ∧
    -- Conséquence 1)
    (∀ l : ℂ, l ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l + c * conj l = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l ^ 2 ∈ LogAlgTilde ∧ ((‖l‖ : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde)) ∧
    -- Conséquence 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ l₁ ^ 2 * l₂ ∈ LogAlgTilde)) ∧
    -- Conséquence 3)
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → ¬ (l ^ 2 ∈ LogAlgTilde ∧ l ^ 3 ∈ LogAlgTilde)) := by
  sorry

end DiazModulus
