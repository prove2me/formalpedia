-- Prove2me | Theorems.Thm_DiazModulus_candidate_sum_div_sq_sub_not_mem_logAlgTilde
-- name    : DiazModulus.candidate_sum_div_sq_sub_not_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:01:20.298472+00:00
-- url     : https://prove2.me/theorems/6309030f-2cc2-42a6-92a0-5518c3d03e9f
-- title:
--   At a candidate u, with Roy's strong six exponentials theorem as hypothesis: if a₁ ≠ a₂ are algebraic with aᵢāᵢ = |u|⁴, then u/(u² − a₁) + u/(u² − a₂) ∉ ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`), $\rho = u\bar u$, and $a_1 \neq a_2$ non-zero algebraic numbers with $a_1\bar a_1 = a_2\bar a_2 = \rho^2$. Then $u/(u^2 - a_1) + u/(u^2 - a_2) \notin \widetilde{\mathcal{L}}$. Here a hypothesis $z \in \widetilde{\mathcal{L}}$ on the sum brings $\bar z$, and the two together give both terms. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** Since $\rho^2/\bar a_i = a_i$, conjugation acts on each $z_i$ by a scalar: $\bar z_i = k_iz_i$ with $k_i = -\rho/\bar a_i$, and $k_1 \neq k_2$. If $z = z_1 + z_2 \in \widetilde{\mathcal{L}}$, then $\bar z = k_1z_1 + k_2z_2 \in \widetilde{\mathcal{L}}$ (`DiazModulus.logAlgTilde_conj_stable`), so $z_1 = (\bar z - k_2z)/(k_1 - k_2)$ and $z_2$ are in $\widetilde{\mathcal{L}}$, against `DiazModulus.candidate_two_pole_not_both_mem_logAlgTilde`.
--
--   **Novelty.** Not asserted: one line from `DiazModulus.candidate_two_pole_not_both_mem_logAlgTilde`, itself a substitution in Diaz (2007, Th. 7(2)).
-- source:
--   One line from a substitution in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(2) (p. 390), which is S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1. Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2) is carried as a hypothesis. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_sum_div_sq_sub_not_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) {a₁ a₂ : ℂ} (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂)
    (h₁ : a₁ * conj a₁ = (u * conj u) ^ 2) (h₂ : a₂ * conj a₂ = (u * conj u) ^ 2) :
    u / (u ^ 2 - a₁) + u / (u ^ 2 - a₂) ∉ LogAlgTilde := by
  sorry

end DiazModulus
