-- Prove2me | Theorems.Thm_DiazModulus_laurent_hull_config_iff
-- name    : DiazModulus.laurent_hull_config_iff
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:09:55.929995+00:00
-- url     : https://prove2.me/theorems/183b9e0a-8947-48a2-bff4-40106fca6b4b
-- title:
--   Laurent hulls: for u transcendental over a subfield K of ℂ and a finite S ⊆ ℤ, span_K{u^s : s ∈ S} carries a p×q configuration iff S contains a sumset A + B with |A| = p, |B| = q
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$ and $u$ transcendental over $K$. For a set $S$ of integers write $V_S = \operatorname{span}_K\{u^s : s \in S\}$ (the Laurent hull of $S$). For a finite $S$ and $p, q \ge 1$, $V_S$ carries a $p \times q$ configuration over $K$ if and only if there are $A, B \subseteq \mathbb{Z}$ with $|A| = p$, $|B| = q$ and $A + B \subseteq S$.
--
--   At a candidate $u$, $u^k \in \widetilde{\mathcal{L}}$ brings $u^{-k} = \rho^{-k}\,\overline{u^k} \in \widetilde{\mathcal{L}}$, so hypotheses on powers of $u$ put Laurent hulls inside $\widetilde{\mathcal{L}}$; this criterion says exactly when Roy's strong six exponentials theorem can refute them through those hulls. The case $S = \{0, \pm 1, \pm k\}$ is `DiazModulus.power_hull_strong_six_exp_configuration_iff`.
--
--   **Proof.** If $A + B \subseteq S$, take $x_i = u^{a_i}$, $y_j = u^{b_j}$; distinct integer powers of $u$ are independent. Conversely, choose $N$ with $S + N \subseteq \mathbb{N}$ and polynomials $P_{ij}$ supported on $S + N$ with $P_{ij}(u) = u^Nx_iy_j$. The spans $V$ of the $P_{i1}$ and $W$ of the $P_{1j}$ have dimensions $p$ and $q$, hence (`DiazModulus.polynomial_submodule_trailing_degrees_card`) exactly $p$ and $q$ orders at $0$. For $f \in V$, $g \in W$, $fg = P_{11}h$ with $h$ a combination of the $P_{ij}$ (both sides agree at $u$), so $\operatorname{ord} f + \operatorname{ord} g - \operatorname{ord} P_{11} - N \in S$; shifting the order set of $V$ gives $A$, and the order set of $W$ is $B$.
--
--   **Novelty.** Not found in the sources read. The nearest printed results are the progression lemma of Fischler (2001, Lemma 6.1) and its repetition in Diaz (2007, Th. 7(2)); the library had the single family $S = \{0, \pm1, \pm k\}$.
-- source:
--   Not found in the sources read; generalises DiazModulus.power_hull_strong_six_exp_configuration_iff. Nearest: S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Pointwise in
theorem laurent_hull_config_iff (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u)
    (S : Finset ℤ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∃ (x : Fin p → ℂ) (y : Fin q → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K ((fun s : ℤ => u ^ s) '' (S : Set ℤ))) ↔
    ∃ A B : Finset ℤ, A.card = p ∧ B.card = q ∧ A + B ⊆ S := by
  sorry

end DiazModulus
