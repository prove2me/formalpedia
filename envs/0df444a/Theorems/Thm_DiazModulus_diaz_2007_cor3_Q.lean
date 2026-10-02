-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor3_Q
-- name    : DiazModulus.diaz_2007_cor3_Q
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:32:13.930812+00:00
-- url     : https://prove2.me/theorems/88f9db7a-19fa-493b-bc78-0e9d13d543fa
-- title:
--   Diaz 2007, Corollaire 3 (Q): quotients outside ℒ̃ and ℒ, under the strong six exponentials theorem
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   1. Let $\lambda_0, \lambda_2, \lambda_3 \in \widetilde{\mathcal{L}}$ with $\lambda_0 \notin \overline{\mathbb{Q}}$ and $(\lambda_0, \lambda_2, \lambda_3)$ linearly independent over $\overline{\mathbb{Q}}$. Then $\lambda_2/\lambda_0$ and $\lambda_3/\lambda_0$ are not both in $\widetilde{\mathcal{L}}$.
--   2. Let $\lambda_0, \lambda_2 \in \widetilde{\mathcal{L}}$ with $\lambda_0 \in (\mathbb{R} \cup i\mathbb{R}) \setminus \overline{\mathbb{Q}}$ and $(\lambda_0, \lambda_2, \bar\lambda_2)$ linearly independent. Then $\lambda_2/\lambda_0 \notin \widetilde{\mathcal{L}}$.
--   3. Let $\lambda_0, \lambda_2 \in \widetilde{\mathcal{L}}$ with $\lambda_0 \in (\mathbb{R} \cup i\mathbb{R}) \setminus \overline{\mathbb{Q}}$ and $\lambda_2 \notin \mathbb{R} \cup i\mathbb{R}$. Then $\lambda_2/\lambda_0 \notin \mathcal{L}$ (this part uses `hB`).
--
--   Diaz's example for part 3, $(1+i)/\pi \notin \mathcal{L}$, is also a case of his unconditional Théorème 4 of 2004 (with $v = 1/\pi$): $e^{v\alpha}$ is transcendental for real $v \neq 0$ and algebraic $\alpha$ off both axes.
--
--   **Proof.** Part 1 is the quotient form of the theorem (`DiazModulus.strong_six_exponentials_iff_quotient_form`) with $\lambda_1 = 1$; part 2 is part 1 of `DiazModulus.diaz_2007_cor1_PQ` with $\lambda_1 = 1$. For part 3, if $\ell = \lambda_2/\lambda_0 \in \mathcal{L}$, then $\ell$ and $\bar\ell = \pm\bar\lambda_2/\lambda_0$ are linearly independent over $\mathbb{Q}$, Baker's theorem makes $1, \ell, \bar\ell$ independent over $\overline{\mathbb{Q}}$, and Corollaire 2 (P) 2) (`DiazModulus.diaz_2007_cor2_P_consequences`) puts $\lambda_0\ell = \lambda_2$ outside $\widetilde{\mathcal{L}}$, which is absurd.
--
--   **Novelty.** None: this is Corollaire 3 (Q) of Diaz (2007), p. 382, with his proof. Diaz notes that parts 1 and 2 are Corollaries 2.3 and 2.8 of Waldschmidt's *Variations on the six exponentials theorem*. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 3 (Q), p. 382, with its proof; parts 1–2 are M. Waldschmidt, Variations on the six exponentials theorem, in: Algebra and Number Theory (Hyderabad), Hindustan Book Agency, 2005, 338–355, Corollaries 2.3 and 2.8. The example of part 3 is also G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorème 4 (p. 539). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 3 (Q)**, parts 1)–3), under Roy's strong six exponentials theorem `hSSE`; part 3)
also uses Baker's theorem `hB`, in its two-logarithm inhomogeneous form. -/
theorem diaz_2007_cor3_Q
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ l₀ l₂ l₃ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde → l₀ ∉ Qbar →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * l₃ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₂ / l₀ ∈ LogAlgTilde ∧ l₃ / l₀ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l₀ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (l₀.im = 0 ∨ l₀.re = 0) → l₀ ∉ Qbar →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l₂ / l₀ ∉ LogAlgTilde) ∧
    -- 3)
    (∀ l₀ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (l₀.im = 0 ∨ l₀.re = 0) → l₀ ∉ Qbar → l₂.re ≠ 0 → l₂.im ≠ 0 →
      l₂ / l₀ ∉ LogAlg) := by
  sorry

end DiazModulus
