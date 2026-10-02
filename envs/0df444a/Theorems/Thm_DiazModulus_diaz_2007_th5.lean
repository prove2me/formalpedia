-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_th5
-- name    : DiazModulus.diaz_2007_th5
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:19.724391+00:00
-- url     : https://prove2.me/theorems/dabe6798-b793-4ffc-bfb2-55a3f05ce425
-- title:
--   Diaz 2007, Théorème 5: u ∈ ℒ̃ keeps v, vu, vu² out of ℒ̃ (strong six exponentials) and out of ℒ (with Baker)
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   1. Let $u \in \mathbb{C}$ and $v \neq 0$ with $(1, v, vu)$ linearly independent over $\overline{\mathbb{Q}}$. If $u \in \widetilde{\mathcal{L}}$, then $v, vu, vu^2$ are not all in $\widetilde{\mathcal{L}}$.
--   2. Let $u \notin \mathbb{Q}$ and $v \neq 0$. If $u \in \widetilde{\mathcal{L}}$, then $v, vu, vu^2$ are not all in $\mathcal{L}$ (this part uses `hB`).
--
--   These are cases of Diaz's conjecture $\{v, vu, vu^2\} \not\subset \widetilde{\mathcal{L}}$, the strong four exponentials conjecture for the proportional families $(1, u)$ and $(v, vu)$.
--
--   **Proof.** Théorème 4 (`DiazModulus.diaz_2007_th4`) with $x = (1, u)$ and $y = (v, vu)$.
--
--   **Novelty.** None: this is Théorème 5 of Diaz (2007), pp. 387–388, with his proof. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 5, pp. 387–388. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Théorème 5**, parts 1) and 2), under Roy's strong six exponentials theorem `hSSE`; part 2)
also uses Baker's theorem `hB`. -/
theorem diaz_2007_th5
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ u v : ℂ, v ≠ 0 →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * v + c * (v * u) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      u ∈ LogAlgTilde → ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ u v : ℂ, (∀ q : ℚ, u ≠ q) → v ≠ 0 →
      u ∈ LogAlgTilde → ¬ (v ∈ LogAlg ∧ v * u ∈ LogAlg ∧ v * u ^ 2 ∈ LogAlg)) := by
  sorry

end DiazModulus
