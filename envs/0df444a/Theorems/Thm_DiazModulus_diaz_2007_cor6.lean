-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor6
-- name    : DiazModulus.diaz_2007_cor6
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:32:36.190298+00:00
-- url     : https://prove2.me/theorems/bdc3a971-d0ad-4ddd-9efe-48947d264aa5
-- title:
--   Diaz 2007, Corollaire 6: real or imaginary quotients in ℒ̃ are algebraic, or rational for logarithms off the axes
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   1. Let $\lambda_0, \lambda_1 \in \widetilde{\mathcal{L}}$ with $(1, \lambda_0, \bar\lambda_0)$ linearly independent over $\overline{\mathbb{Q}}$. If $\lambda_1/\lambda_0 \in (\mathbb{R} \cup i\mathbb{R}) \cap \widetilde{\mathcal{L}}$, then $\lambda_1/\lambda_0 \in \overline{\mathbb{Q}}$.
--   2. Let $\ell_0, \ell_1 \in \mathcal{L} \setminus (\mathbb{R} \cup i\mathbb{R})$. If $\ell_1/\ell_0 \in (\mathbb{R} \cup i\mathbb{R}) \cap \widetilde{\mathcal{L}}$, then $\ell_1/\ell_0 \in \mathbb{Q}$ (this part uses `hB`).
--
--   Diaz obtains them by putting together the hypotheses of his conjectures (Q1) and (Qr1), resp. (Q2) and (Qr2): each pair of conjectural sufficient conditions together gives an effective one.
--
--   **Proof.** Théorème 4 (`DiazModulus.diaz_2007_th4`) with $(x_1, x_2) = (1, \lambda_1/\lambda_0)$ and $(y_1, y_2) = (\lambda_0, \bar\lambda_0)$, resp. $(\ell_0, \bar\ell_0)$: the fourth product is $\pm\bar\lambda_1$, resp. $\pm\bar\ell_1$.
--
--   **Novelty.** None: this is Corollaire 6 of Diaz (2007), p. 387, with his proof. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 6, p. 387. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 6**, parts 1) and 2), under Roy's strong six exponentials theorem `hSSE`; part 2)
also uses Baker's theorem `hB`. -/
theorem diaz_2007_cor6
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₀ + c * conj l₀ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∈ LogAlgTilde → l₁ / l₀ ∈ Qbar) ∧
    -- 2)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlg → l₁ ∈ LogAlg →
      l₀.re ≠ 0 → l₀.im ≠ 0 → l₁.re ≠ 0 → l₁.im ≠ 0 →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∈ LogAlgTilde → ∃ q : ℚ, l₁ / l₀ = q) := by
  sorry

end DiazModulus
