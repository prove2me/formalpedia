-- Prove2me | Theorems.Thm_DiazModulus_candidate_two_pole_not_both_mem_logAlgTilde
-- name    : DiazModulus.candidate_two_pole_not_both_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-09T09:00:53.848991+00:00
-- url     : https://prove2.me/theorems/9c51926f-f543-4223-ad7d-e06913f68e74
-- title:
--   At a candidate u, with Roy's strong six exponentials theorem as hypothesis: for distinct non-zero algebraic a₁, a₂, u/(u² − a₁) and u/(u² − a₂) are not both in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`) and $a_1 \neq a_2$ non-zero algebraic numbers. Then $u/(u^2 - a_1)$ and $u/(u^2 - a_2)$ are not both in $\widetilde{\mathcal{L}}$. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** $\rho = |u|^2$ is algebraic and $u \notin \overline{\mathbb{Q}}$ (`DiazModulus.hermite_lindemann_holds`); $u, \bar u \in \mathcal{L}$ (`DiazModulus.logAlg_conj_stable`) and $1 \in \widetilde{\mathcal{L}}$. If $z_1, z_2 \in \widetilde{\mathcal{L}}$, then $W \subseteq \widetilde{\mathcal{L}}$, and the configuration of `DiazModulus.circle_point_two_pole_extension_carries_two_by_three_configuration` contradicts `hSSE`.
--
--   **Novelty.** Not asserted: it is one substitution in Diaz (2007, Th. 7(2)), that is Fischler (2001, Lemma 6.1), with ratio $u^2$ and first term $b$; Diaz (2004, Th. 2) at $x = (u, \bar u)$ also gives it after a case split.
-- source:
--   One substitution in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(2) (p. 390), which is S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184); also G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), at x = (u, ū). Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2) is carried as a hypothesis. Formal proof: Diaz modulus mission, 9 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_two_pole_not_both_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) {a₁ a₂ : ℂ} (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    ¬ (u / (u ^ 2 - a₁) ∈ LogAlgTilde ∧ u / (u ^ 2 - a₂) ∈ LogAlgTilde) := by
  sorry

end DiazModulus
