-- Prove2me | Theorems.Thm_DiazModulus_two_by_three_configuration_forces_progression
-- name    : DiazModulus.two_by_three_configuration_forces_progression
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-05T07:47:32.776982+00:00
-- url     : https://prove2.me/theorems/46109c0d-3af4-46c3-900b-441e398cde5e
-- title:
--   A 2×3 configuration in a space of dimension at most 4 forces a geometric progression: V = Q̄b + Q̄bh + Q̄bh² + Q̄bh³ with b ≠ 0 and h ∉ Q̄
-- statement:
--   Let $V \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension at most $4$. Suppose there are $x_1, x_2 \in \mathbb{C}$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3 \in \mathbb{C}$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_i y_j$ in $V$. Then there are $b \neq 0$ and $h \notin \overline{\mathbb{Q}}$ with
--   $$V = \overline{\mathbb{Q}}\,b + \overline{\mathbb{Q}}\,bh + \overline{\mathbb{Q}}\,bh^2 + \overline{\mathbb{Q}}\,bh^3 .$$
--   In particular $V$ has dimension exactly $4$.
--
--   Conversely, such a progression carries the configuration $x = (1, h)$, $y = (b, bh, bh^2)$. With Roy's strong six exponentials theorem, Fischler (2001, Lemma 6.1) and Diaz (2007, Th. 7(2)) use that direction to show that four non-zero elements of $\widetilde{\mathcal{L}}$ never form a geometric progression with transcendental ratio. The statement here is the other direction; it is the step that forces the shape in `DiazModulus.circle_point_extension_two_by_three_configuration_iff`.
--
--   **Proof.** Put $h = x_2/x_1$. Then $h \notin \overline{\mathbb{Q}}$ because $x_1, x_2$ are independent, so no non-zero polynomial over $\overline{\mathbb{Q}}$ vanishes at $h$. Let $B = x_1(\overline{\mathbb{Q}}y_1 + \overline{\mathbb{Q}}y_2 + \overline{\mathbb{Q}}y_3)$, of dimension $3$. Both $B$ and $hB$ lie in $V$, so $B + hB$ has dimension at most $4$ and $W = B \cap hB$ has dimension at least $2$. The spaces $W$ and $h^{-1}W$ lie in $B$ and have dimension at least $2$, so they meet in some $c \neq 0$. Writing $c = hb$ with $b \in B$ gives $b, hb, h^2b \in B$, hence $b, bh, bh^2, bh^3 \in V$. These four are independent because $h$ is transcendental, so they span $V$.
--
--   **Novelty.** That a configuration forces a progression was not found in the sources read. The progression itself, and the configuration it carries, are those of Fischler (2001, Lemma 6.1) and Diaz (2007, Th. 7(2)).
-- source:
--   The converse direction (a progression carries a configuration) is used in S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184), and in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(2) (p. 390). This direction was not found in the sources read. Formal proof: Diaz modulus mission, 5 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem two_by_three_configuration_forces_progression (V : Submodule (↥Qbar) ℂ)
    [FiniteDimensional (↥Qbar) V] (hV : Module.finrank (↥Qbar) V ≤ 4)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ V) :
    ∃ b h : ℂ, b ≠ 0 ∧ h ∉ Qbar ∧
      V = Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)) := by
  sorry

end DiazModulus
