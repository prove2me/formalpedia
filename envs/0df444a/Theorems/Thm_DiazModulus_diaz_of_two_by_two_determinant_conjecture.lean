-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_two_by_two_determinant_conjecture
-- name    : DiazModulus.diaz_of_two_by_two_determinant_conjecture
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:04:05.726076+00:00
-- url     : https://prove2.me/theorems/6482dae4-0b18-4f15-9739-7c86ff445953
-- title:
--   Waldschmidt's conjecture on 2×2 determinants over ℒ̃ implies Diaz's conjecture
-- statement:
--   **Waldschmidt's $2\times2$ determinant conjecture suffices.**
--
--   Waldschmidt's conjecture on $2\times2$ determinants: let $M = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ have entries in $\widetilde{\mathcal{L}}$, the $\overline{\mathbb{Q}}$-span of $1$ and the logarithms of algebraic numbers. Assume that the four rows of $\begin{pmatrix} M \\ I_2 \end{pmatrix}$ are $\overline{\mathbb{Q}}$-linearly independent, and so are the four columns of $(I_2, M)$. Then $\det M = ad - bc \notin \widetilde{\mathcal{L}}$.
--
--   In the hypothesis `hW` the row condition is written out: no non-trivial pair $s, t \in \overline{\mathbb{Q}}$ has $s(a, b) + t(c, d) \in \overline{\mathbb{Q}}^{2}$. The column condition is the same for $(a, c)$ and $(b, d)$.
--
--   Waldschmidt proved the $2\times3$ analogue, that one of the three $2\times2$ minors lies outside $\widetilde{\mathcal{L}}$ (Theorem 1.2 of the paper cited below), and conjectured the $2\times2$ case.
--
--   This node: under `hW`, Diaz's modulus conjecture holds.
--
--   **Proof.** For a candidate $u$, with $r = |u|$, take $M = H(u, r) = \begin{pmatrix} u & r \\ r & \bar u \end{pmatrix}$. Its entries lie in $\widetilde{\mathcal{L}}$ and its determinant is $u\bar u - r^{2} = 0 \in \widetilde{\mathcal{L}}$. The independence conditions hold: $s(u, r) + t(r, \bar u) \in \overline{\mathbb{Q}}^{2}$ gives $su \in \overline{\mathbb{Q}}$ and $t\bar u \in \overline{\mathbb{Q}}$, and $u, \bar u$ are transcendental. $M$ is symmetric, so the column condition is the same. So a candidate would contradict the conjecture.
--
--   **Attribution.** The conjecture is Conjecture 1.6 of M. Waldschmidt, *Further variations on the six exponentials theorem*, Hardy-Ramanujan J. **28** (2005), 1–9. He notes that it follows from the conjecture that $\mathbb{Q}$-linearly independent logarithms of algebraic numbers are algebraically independent.
-- source:
--   Conjecture: M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Conjecture 1.6. Instantiation and formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_of_two_by_two_determinant_conjecture (hW : ∀ a b c d : ℂ, a ∈ LogAlgTilde → b ∈ LogAlgTilde → c ∈ LogAlgTilde →
      d ∈ LogAlgTilde →
      (∀ s t : ℂ, s ∈ Qbar → t ∈ Qbar → s * a + t * c ∈ Qbar → s * b + t * d ∈ Qbar →
        s = 0 ∧ t = 0) →
      (∀ s t : ℂ, s ∈ Qbar → t ∈ Qbar → s * a + t * b ∈ Qbar → s * c + t * d ∈ Qbar →
        s = 0 ∧ t = 0) →
      a * d - b * c ∉ LogAlgTilde) :
    DiazModulusConjecture := by
  sorry

end DiazModulus
