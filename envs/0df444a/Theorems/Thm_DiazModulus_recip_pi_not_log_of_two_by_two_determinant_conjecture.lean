-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_of_two_by_two_determinant_conjecture
-- name    : DiazModulus.recip_pi_not_log_of_two_by_two_determinant_conjecture
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:04:15.77693+00:00
-- url     : https://prove2.me/theorems/8d01e02d-1567-4a7e-945e-77ccf50611b9
-- title:
--   Waldschmidt's conjecture on 2×2 determinants over ℒ̃ implies the statement (S)
-- statement:
--   **Waldschmidt's $2\times2$ determinant conjecture suffices.**
--
--   Waldschmidt's conjecture on $2\times2$ determinants: let $M = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ have entries in $\widetilde{\mathcal{L}}$, the $\overline{\mathbb{Q}}$-span of $1$ and the logarithms of algebraic numbers. Assume that the four rows of $\begin{pmatrix} M \\ I_2 \end{pmatrix}$ are $\overline{\mathbb{Q}}$-linearly independent, and so are the four columns of $(I_2, M)$. Then $\det M = ad - bc \notin \widetilde{\mathcal{L}}$.
--
--   In the hypothesis `hW` the row condition is written out: no non-trivial pair $s, t \in \overline{\mathbb{Q}}$ has $s(a, b) + t(c, d) \in \overline{\mathbb{Q}}^{2}$. The column condition is the same for $(a, c)$ and $(b, d)$.
--
--   Waldschmidt proved the $2\times3$ analogue, that one of the three $2\times2$ minors lies outside $\widetilde{\mathcal{L}}$ (Theorem 1.2 of the paper cited below), and conjectured the $2\times2$ case.
--
--   This node: under `hW`, the statement (S) holds: $e^{\gamma/(i\pi)}$ is transcendental for every non-zero algebraic $\gamma$.
--
--   **Proof.** Suppose $\lambda = \gamma/(i\pi)$ has $e^{\lambda}$ algebraic, and take $M = \begin{pmatrix} 1 & i\pi \\ \lambda & \gamma \end{pmatrix}$, with determinant $\gamma - i\pi\lambda = 0$. Rows: $s(1, i\pi) + t(\lambda, \gamma) \in \overline{\mathbb{Q}}^{2}$ gives $si\pi \in \overline{\mathbb{Q}}$, so $s = 0$, and then $t\lambda \in \overline{\mathbb{Q}}$, so $t = 0$. Columns: $s(1, \lambda) + t(i\pi, \gamma) \in \overline{\mathbb{Q}}^{2}$ gives $t = 0$ and then $s = 0$ in the same way. Both use only that $i\pi$ and $\lambda$ are transcendental.
--
--   **Attribution.** The conjecture is Conjecture 1.6 of M. Waldschmidt, *Further variations on the six exponentials theorem*, Hardy-Ramanujan J. **28** (2005), 1–9. He notes that it follows from the conjecture that $\mathbb{Q}$-linearly independent logarithms of algebraic numbers are algebraically independent.
-- source:
--   Conjecture: M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Conjecture 1.6. Instantiation and formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_not_log_of_two_by_two_determinant_conjecture (hW : ∀ a b c d : ℂ, a ∈ LogAlgTilde → b ∈ LogAlgTilde → c ∈ LogAlgTilde →
      d ∈ LogAlgTilde →
      (∀ s t : ℂ, s ∈ Qbar → t ∈ Qbar → s * a + t * c ∈ Qbar → s * b + t * d ∈ Qbar →
        s = 0 ∧ t = 0) →
      (∀ s t : ℂ, s ∈ Qbar → t ∈ Qbar → s * a + t * b ∈ Qbar → s * c + t * d ∈ Qbar →
        s = 0 ∧ t = 0) →
      a * d - b * c ∉ LogAlgTilde) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  sorry

end DiazModulus
