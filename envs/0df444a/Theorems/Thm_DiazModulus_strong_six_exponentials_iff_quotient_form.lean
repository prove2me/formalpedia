-- Prove2me | Theorems.Thm_DiazModulus_strong_six_exponentials_iff_quotient_form
-- name    : DiazModulus.strong_six_exponentials_iff_quotient_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:40.977858+00:00
-- url     : https://prove2.me/theorems/ca143d66-3bb0-4d70-a157-903cd191ff1b
-- title:
--   Diaz 2007, Théorème 3: the strong six exponentials theorem is equivalent to its quotient form
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$.
--
--   The following two statements are equivalent.
--
--   1. For $\overline{\mathbb{Q}}$-linearly independent $x_1, x_2$ and $\overline{\mathbb{Q}}$-linearly independent $y_1, y_2, y_3$, one of the six numbers $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--   2. For $\lambda_0, \lambda_1, \lambda_2, \lambda_3 \in \widetilde{\mathcal{L}}$ with $(\lambda_0, \lambda_1)$ and $(\lambda_0, \lambda_2, \lambda_3)$ both $\overline{\mathbb{Q}}$-linearly independent, one of $\lambda_1\lambda_2/\lambda_0$ and $\lambda_1\lambda_3/\lambda_0$ is not in $\widetilde{\mathcal{L}}$.
--
--   Statement 1 is Roy's strong six exponentials theorem; statement 2 is the form in which most of its consequences are used. No hypothesis is assumed here: the node proves the equivalence.
--
--   **Proof.** From 1 to 2, take $x = (1, \lambda_1/\lambda_0)$ and $y = (\lambda_0, \lambda_2, \lambda_3)$: the six products are $\lambda_0, \lambda_2, \lambda_3, \lambda_1, \lambda_1\lambda_2/\lambda_0, \lambda_1\lambda_3/\lambda_0$. From 2 to 1, take $\lambda_0 = x_1y_1$, $\lambda_1 = x_2y_1$, $\lambda_2 = x_1y_2$, $\lambda_3 = x_1y_3$, so that $\lambda_1\lambda_2/\lambda_0 = x_2y_2$ and $\lambda_1\lambda_3/\lambda_0 = x_2y_3$.
--
--   **Novelty.** None: this is Théorème 3 of Diaz (2007), versions 1 and 3, with his proof of their equivalence (pp. 379–380). Diaz notes that version 3 is Corollary 2.6 of Waldschmidt's *Variations on the six exponentials theorem*. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 3, versions 1 and 3 (p. 379), proof p. 380. Version 1 is D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Corollary 2 of §4; see also M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Corollary 11.16. Version 3 is M. Waldschmidt, Variations on the six exponentials theorem, in: Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Corollary 2.6. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Théorème 3, versions 1 and 3.** Roy's strong six exponentials theorem (left) is equivalent to
its four-logarithm quotient form (right). -/
theorem strong_six_exponentials_iff_quotient_form :
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) ↔
    (∀ l₀ l₁ l₂ l₃ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      l₃ ∈ LogAlgTilde →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₀ + b * l₁ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * l₃ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ / l₀ ∈ LogAlgTilde ∧ l₁ * l₃ / l₀ ∈ LogAlgTilde)) := by
  sorry

end DiazModulus
