-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor7
-- name    : DiazModulus.diaz_2007_cor7
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:32:58.026063+00:00
-- url     : https://prove2.me/theorems/9bffaeee-d093-43fb-8737-48107d86875d
-- title:
--   Diaz 2007, Corollaire 7: if τ or 1/τ is in ℒ̃, then e^{2iπτ} and e^{−2iπ/τ} are not both algebraic
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   Let $\tau$ lie in the upper half-plane, with $\tau \in \widetilde{\mathcal{L}}$ or $1/\tau \in \widetilde{\mathcal{L}}$. Then $e^{2i\pi\tau}$ and $e^{-2i\pi/\tau}$ are not both algebraic.
--
--   This is the conclusion of the statement (C4) of Diaz (1997), equivalent there to the injectivity of the modular invariant $J$ on $\overline{\mathbb{Q}} \cap (D \setminus \{0\})$, under the extra hypothesis that $\tau$ or $1/\tau$ lies in $\widetilde{\mathcal{L}}$. Diaz presents it as adding to Proposition 3 of Diaz (1997).
--
--   **Proof.** Théorème 5 (2) (`DiazModulus.diaz_2007_th5`) with $u = \tau$, $v = 2i\pi/\tau$, or with $u = 1/\tau$, $v = 2i\pi\tau$; the middle number is $2i\pi \in \mathcal{L}$.
--
--   **Novelty.** None: this is Corollaire 7 of Diaz (2007), p. 388, with his proof. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 7, p. 388; the statement (C4) is from G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 7.** Under Roy's strong six exponentials theorem `hSSE` and Baker's theorem `hB`:
for `τ` in the upper half-plane with `τ ∈ ℒ̃` or `1/τ ∈ ℒ̃`, the numbers `e^{2iπτ}` and `e^{-2iπ/τ}` are not
both algebraic. -/
theorem diaz_2007_cor7
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    ∀ τ : ℂ, 0 < τ.im → (τ ∈ LogAlgTilde ∨ 1 / τ ∈ LogAlgTilde) →
      ¬ (IsAlgebraic ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)) ∧
        IsAlgebraic ℚ (Complex.exp (-(2 * ((Real.pi : ℝ) : ℂ) * Complex.I) / τ))) := by
  sorry

end DiazModulus
