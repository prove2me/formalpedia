-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_th6
-- name    : DiazModulus.diaz_2007_th6
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:00.143738+00:00
-- url     : https://prove2.me/theorems/8cccd0dd-d4a0-4e7f-ba97-cd61ca9df115
-- title:
--   Diaz 2007, Théorème 6: when (1, u, ū) is dependent, v, vu, vu² are not all in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   1. Let $u, v \notin \overline{\mathbb{Q}}$ with $(v, \bar v)$ independent and $(1, u, \bar u)$ dependent over $\overline{\mathbb{Q}}$. Then $v, vu, vu^2$ are not all in $\widetilde{\mathcal{L}}$.
--   2. Let $\lambda \in \widetilde{\mathcal{L}}$ and $t \notin \overline{\mathbb{Q}}$ with $(\lambda/t, \overline{\lambda/t})$ independent and $(1, t, \bar t)$ dependent. Then $t\lambda$ and $\lambda/t$ are not both in $\widetilde{\mathcal{L}}$.
--   3. Let $\lambda \in \widetilde{\mathcal{L}}$ and $s \notin \overline{\mathbb{Q}}$ with $(\lambda, \bar\lambda)$ independent and $(1, s, \bar s)$ dependent. Then $s\lambda$ and $s^2\lambda$ are not both in $\widetilde{\mathcal{L}}$.
--   4. Let $\lambda, \lambda_1, \lambda_2 \in \widetilde{\mathcal{L}} \setminus \{0\}$ with $\lambda_1\lambda_2 = \lambda^2$, $(\lambda_1, \bar\lambda_1)$ independent and $(1, \lambda/\lambda_1, \overline{\lambda/\lambda_1})$ dependent. Then $\lambda/\lambda_1 = \lambda_2/\lambda \in \overline{\mathbb{Q}}$.
--
--   Part 2 generalises Proposition 3 of Diaz (1997), with $\widetilde{\mathcal{L}}$ in place of $\mathcal{L}$ and $\lambda$ in place of $2i\pi$.
--
--   **Proof.** Part 1 applies the theorem to $(v, \bar v)$ and $(1, u, u^2)$: writing $\bar u = \alpha + \beta u$, the numbers $v\bar u$ and $v\bar u^2$ are combinations of $v, vu, vu^2$, and their conjugates complete the six products. Parts 2–4 are part 1 at $(u, v) = (t, \lambda/t)$, $(s, \lambda)$ and $(\lambda/\lambda_1, \lambda_1)$.
--
--   **Novelty.** None: this is Théorème 6 of Diaz (2007), p. 389, with his proof (pp. 389–390). The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 6, p. 389, proof pp. 389–390. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Théorème 6**, parts 1)–4), under Roy's strong six exponentials theorem `hSSE`. -/
theorem diaz_2007_th6
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ u v : ℂ, u ∉ Qbar → v ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * u + c * conj u = 0) →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l t : ℂ, l ∈ LogAlgTilde → t ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * (l / t) + b * conj (l / t) = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * t + c * conj t = 0) →
      ¬ (t * l ∈ LogAlgTilde ∧ l / t ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l s : ℂ, l ∈ LogAlgTilde → s ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * s + c * conj s = 0) →
      ¬ (s * l ∈ LogAlgTilde ∧ s ^ 2 * l ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l l₁ l₂ : ℂ, l ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      l ≠ 0 → l₁ ≠ 0 → l₂ ≠ 0 → l₁ * l₂ = l ^ 2 →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * conj l₁ = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * (l / l₁) + c * conj (l / l₁) = 0) →
      l / l₁ = l₂ / l ∧ l / l₁ ∈ Qbar) := by
  sorry

end DiazModulus
