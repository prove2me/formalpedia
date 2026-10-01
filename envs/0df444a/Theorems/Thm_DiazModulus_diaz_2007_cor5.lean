-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_cor5
-- name    : DiazModulus.diaz_2007_cor5
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:09.326209+00:00
-- url     : https://prove2.me/theorems/5df0a3e9-4119-4eca-8d37-5abc9a365fa9
-- title:
--   Diaz 2007, Corollaire 5: λ/λ̄, λ²/λ̄ and shifted reciprocals outside ℒ̃, under the strong six exponentials theorem
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $\lambda \in \widetilde{\mathcal{L}} \setminus \overline{\mathbb{Q}}$.
--
--   1. If $(\lambda, \bar\lambda, \lambda\bar\lambda)$ is linearly independent over $\overline{\mathbb{Q}}$, then $\lambda/\bar\lambda \notin \widetilde{\mathcal{L}}$.
--   2. If $(\lambda, \bar\lambda)$ is linearly independent, then $\lambda^2/\bar\lambda \notin \widetilde{\mathcal{L}}$.
--   3. If $(\lambda, \bar\lambda)$ is linearly independent and $(1, \lambda, \bar\lambda)$ is not, then $1/\lambda \notin \widetilde{\mathcal{L}}$.
--   4. For every algebraic $\alpha \neq 0$, $1/\lambda$ and $1/(\lambda + \alpha)$ are not both in $\widetilde{\mathcal{L}}$.
--
--   At a candidate $u$ of Diaz's conjecture, $u^2/\bar u = u^3/|u|^2$, so part 2 gives $u^3 \notin \widetilde{\mathcal{L}}$ (`DiazModulus.candidate_cube_and_axis_multiple_not_mem_logAlgTilde`).
--
--   **Proof.** From `DiazModulus.diaz_2007_cor4`: parts 1 and 2 are its parts 2 and 3 at $(\lambda, \bar\lambda)$, where the two numbers are conjugate; part 3 writes $\bar\lambda = \alpha + \beta\lambda$ with $\alpha, \beta \neq 0$ and uses $\bar\lambda/\lambda = \beta + \alpha/\lambda$; part 4 is its part 2 at $(\lambda, \lambda + \alpha)$.
--
--   **Novelty.** None: this is Corollaire 5 of Diaz (2007), p. 383, with his proof (pp. 383–384). The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 5, p. 383, proof pp. 383–384. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Corollaire 5**, parts 1)–4), for `l ∈ ℒ̃ ∖ Q̄`, under Roy's strong six exponentials theorem
`hSSE`. -/
theorem diaz_2007_cor5
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {l : ℂ} (hl : l ∈ LogAlgTilde) (hlQ : l ∉ Qbar) :
    -- 1)
    ((∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l + b * conj l + c * (l * conj l) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l / conj l ∉ LogAlgTilde) ∧
    -- 2)
    ((∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      l ^ 2 / conj l ∉ LogAlgTilde) ∧
    -- 3)
    ((∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * l + c * conj l = 0) →
      1 / l ∉ LogAlgTilde) ∧
    -- 4)
    (∀ α : ℂ, α ∈ Qbar → α ≠ 0 → ¬ (1 / l ∈ LogAlgTilde ∧ 1 / (l + α) ∈ LogAlgTilde)) := by
  sorry

end DiazModulus
