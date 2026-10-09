-- Prove2me | Theorems.Thm_DiazModulus_power_pair_hull_two_by_three_iff
-- name    : DiazModulus.power_pair_hull_two_by_three_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:10:04.01121+00:00
-- url     : https://prove2.me/theorems/41b0da9a-8258-4cd0-9035-a24bd38c09d3
-- title:
--   For u transcendental over a subfield K of ℂ and integers 4 ≤ k < l, span_K{u^s : s ∈ {0, ±1, ±k, ±l}} carries a 2×3 configuration iff l ∈ {k+1, k+2, 2k−1, 2k, 2k+1, 3k}
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$, $u$ transcendental over $K$, and $4 \le k < l$ integers. The span of $u^s$, $s \in \{0, \pm1, \pm k, \pm l\}$, carries a $2 \times 3$ configuration over $K$ if and only if $l \in \{k + 1, k + 2, 2k - 1, 2k, 2k + 1, 3k\}$.
--
--   So at a candidate, Roy's strong six exponentials theorem applied through this hull excludes exactly these pairs $u^k, u^l \in \widetilde{\mathcal{L}}$ (`DiazModulus.candidate_power_pair_not_both_mem_logAlgTilde`) and says nothing about the others.
--
--   **Proof.** Compose `DiazModulus.laurent_hull_config_iff` ($p = 2$, $q = 3$), `DiazModulus.two_sumset_iff_difference_count` and `DiazModulus.power_pair_difference_count_iff`.
--
--   **Novelty.** Not found in the sources read; it is short. The exclusions themselves are Diaz (2007) by substitution; what is added is that the list is complete for this hull.
-- source:
--   Not found in the sources read (the exclusions it yields are substitutions in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem power_pair_hull_two_by_three_iff (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u)
    (k l : ℤ) (hk : 4 ≤ k) (hkl : k < l) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K
        ((fun s : ℤ => u ^ s) '' ({0, 1, -1, k, -k, l, -l} : Set ℤ))) ↔
    (l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) := by
  sorry

end DiazModulus
