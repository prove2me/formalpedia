-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_th7
-- name    : DiazModulus.diaz_2007_th7
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:25.347977+00:00
-- url     : https://prove2.me/theorems/cb68b012-844f-4b0e-8f77-cb2c6b85a330
-- title:
--   Diaz 2007, Théorème 7: {v, vu, vū} and {v, vu, vu², vu³} are not inside ℒ̃; in particular u, u², u³ are not all in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   1. Let $(1, u, \bar u)$ and $(v, \bar v)$ be linearly independent over $\overline{\mathbb{Q}}$. Then $v, vu, v\bar u$ are not all in $\widetilde{\mathcal{L}}$.
--   2. Let $u \notin \overline{\mathbb{Q}}$ and $v \neq 0$. Then $v, vu, vu^2, vu^3$ are not all in $\widetilde{\mathcal{L}}$. In particular $u, u^2, u^3$ are not all in $\widetilde{\mathcal{L}}$.
--
--   Diaz's examples: $\pi^{1/2}$ and $\pi^{3/2}$, and $\pi^{1/3}$ and $\pi^{2/3}$, are not both in $\widetilde{\mathcal{L}}$.
--
--   **Proof.** The theorem applied to $(v, \bar v)$ and $(1, u, \bar u)$, whose conjugate products complete the six; and to $(v, vu)$ and $(1, u, u^2)$.
--
--   **Novelty.** None: this is Théorème 7 of Diaz (2007), p. 390, with his proof. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 7, p. 390. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **Diaz 2007, Théorème 7**, parts 1) and 2) with the "in particular", under Roy's strong six exponentials
theorem `hSSE`. -/
theorem diaz_2007_th7
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ u v : ℂ,
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * u + c * conj u = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0) →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * conj u ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ u v : ℂ, u ∉ Qbar → v ≠ 0 →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde ∧ v * u ^ 3 ∈ LogAlgTilde)) ∧
    (∀ u : ℂ, u ∉ Qbar → ¬ (u ∈ LogAlgTilde ∧ u ^ 2 ∈ LogAlgTilde ∧ u ^ 3 ∈ LogAlgTilde)) := by
  sorry

end DiazModulus
