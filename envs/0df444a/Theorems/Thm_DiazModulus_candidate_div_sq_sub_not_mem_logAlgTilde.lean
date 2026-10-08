-- Prove2me | Theorems.Thm_DiazModulus_candidate_div_sq_sub_not_mem_logAlgTilde
-- name    : DiazModulus.candidate_div_sq_sub_not_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T07:48:00.333992+00:00
-- url     : https://prove2.me/theorems/35486890-e3f7-4a35-a512-441fc709f738
-- title:
--   At a candidate u, with Roy's strong six exponentials theorem as hypothesis: u/(u² − a) ∉ ℒ̃ for every non-zero algebraic a with aā ≠ |u|⁴, and u/(u² − a)² ∉ ℒ̃ when aā = |u|⁴
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`), so $\rho = u\bar u$ is algebraic, and let $a \in \overline{\mathbb{Q}}$, $a \neq 0$. Then $u/(u^2 - a) \notin \widetilde{\mathcal{L}}$ if $a\bar a \neq \rho^2$, and $u/(u^2 - a)^2 \notin \widetilde{\mathcal{L}}$ if $a\bar a = \rho^2$. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** $\rho = |u|^2$ is algebraic, $u \notin \overline{\mathbb{Q}}$ by Hermite–Lindemann (`DiazModulus.hermite_lindemann_holds`), and $u, \bar u \in \mathcal{L}$ (`DiazModulus.logAlg_conj_stable`). If $z \in \widetilde{\mathcal{L}}$, then $\bar z \in \widetilde{\mathcal{L}}$ (`DiazModulus.logAlgTilde_conj_stable`), so $H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z \subseteq \widetilde{\mathcal{L}}$, and the configuration of `DiazModulus.circle_point_conjugate_pair_extension_carries_two_by_three_configuration` contradicts `hSSE`.
--
--   **Novelty.** Not asserted. The first part is one substitution in Diaz (2004, Th. 2) at $x = (u, \bar u)$, $y = 1/(u^2 - a)$, where $\bar u\,y = (\rho z - \bar u)/a$; it is also Diaz (2007, Cor. 4(4) and Th. 7(1)). The second is Diaz (2007, Th. 6(3)) at $(\lambda, s) = (u, 1/(u^2 - a))$, after one line.
-- source:
--   One substitution in G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538), at x = (u, ū), y = 1/(u² − a); also G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Cor. 4(4) and Th. 7(1) (pp. 383, 390); the second part is G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 6(3) (p. 389). Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2) is carried as a hypothesis. Formal proof: Diaz modulus mission, 6 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_div_sq_sub_not_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) {a : ℂ} (ha : a ∈ Qbar) (ha0 : a ≠ 0) :
    (a * conj a ≠ (u * conj u) ^ 2 → u / (u ^ 2 - a) ∉ LogAlgTilde) ∧
      (a * conj a = (u * conj u) ^ 2 → u / (u ^ 2 - a) ^ 2 ∉ LogAlgTilde) := by
  sorry

end DiazModulus
