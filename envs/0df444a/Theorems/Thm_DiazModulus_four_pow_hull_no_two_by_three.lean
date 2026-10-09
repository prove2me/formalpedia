-- Prove2me | Theorems.Thm_DiazModulus_four_pow_hull_no_two_by_three
-- name    : DiazModulus.four_pow_hull_no_two_by_three
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:09:56.047126+00:00
-- url     : https://prove2.me/theorems/6c47ce09-6fa5-4025-90d3-ec6ef78e2208
-- title:
--   For u transcendental over a subfield K of ℂ, span_K{u^s : s ∈ {0, ±1} ∪ {±4^j : j ≥ 1}} carries no 2×3 configuration
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$ and $u$ transcendental over $K$. The span of the powers $u^s$ with $s \in \{0, \pm1\} \cup \{\pm 4^j : j \ge 1\}$ carries no $2 \times 3$ configuration over $K$.
--
--   At a candidate, the hypothesis "$u^{4^j} \in \widetilde{\mathcal{L}}$ for every $j \ge 1$" puts this whole hull inside $\widetilde{\mathcal{L}}$ (by conjugation). So Roy's strong six exponentials theorem, used through Laurent hulls, cannot exclude it, although it excludes many pairs of powers (`DiazModulus.power_pair_hull_two_by_three_iff`). Nothing is claimed about other configurations in $\widetilde{\mathcal{L}}$.
--
--   **Proof.** The six products lie in the span of finitely many of the powers, so by `DiazModulus.laurent_hull_config_iff` and `DiazModulus.two_sumset_iff_difference_count` some $d > 0$ would have three $s$ with $s, s + d$ in the exponent set $T$. The non-zero absolute values in $T$ are powers of $4$, so two of them are equal or differ by a factor at least $4$. For a pair $s < s + d$ in $T$ with $M = \max(|s|, |s + d|)$, either $s = -M$ and $d = 2M$, or $|d - M| \le M/4$ and $s \in \{M - d, -M\}$; the factor-$4$ gap forces the same $M$ and the same case for all pairs with difference $d$, so $s$ takes at most two values.
--
--   **Novelty.** Not found in the sources read (not in Diaz 2007, whose p. 390 summary only says the six exponentials route will not go far, nor in Fischler 2001); it is short.
-- source:
--   Not found in the sources read (G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, p. 390; S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem four_pow_hull_no_two_by_three (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K ((fun s : ℤ => u ^ s) ''
        {s : ℤ | s = 0 ∨ s = 1 ∨ s = -1 ∨ ∃ j : ℕ, 1 ≤ j ∧ (s = 4 ^ j ∨ s = -4 ^ j)}) := by
  sorry

end DiazModulus
