-- Prove2me | Theorems.Thm_DiazModulus_generic_conj_pair_four_exp_barrier
-- name    : DiazModulus.generic_conj_pair_four_exp_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T20:37:14.460982+00:00
-- url     : https://prove2.me/theorems/7d4a06b0-0c88-4474-892f-16c8ec61a80e
-- title:
--   The four exponentials conjecture has no instance on the logarithms certified by a generic candidate
-- statement:
--   **A barrier: the four exponentials conjecture sees nothing homogeneous.**
--
--   Let $u \neq 0$ with $|u|^{2}$ algebraic, algebraically independent of $i\pi$ over $\overline{\mathbb{Q}}$. Let $M$ be a $2\times2$ matrix whose entries are rational linear combinations of $u$, $\bar u$ and $i\pi$. If $\det M = 0$, then the rows of $M$ are $\mathbb{Q}$-linearly dependent or its columns are.
--
--   For a candidate $u$ of Diaz's conjecture, the numbers $u$, $\bar u$ and $i\pi$ are the logarithms of algebraic numbers that the candidate certifies. The statement therefore says that no instance of the four exponentials conjecture ($\mathbb{Q}$-independent rows and columns, products in $\mathcal{L}$) can be built from them: on this data the conjecture is a theorem, by pure algebra. What does detect a candidate is a configuration with a constant entry, as in `DiazModulus.diaz_of_sfe`. For candidates algebraic over $\mathbb{Q}(\pi)$, see `DiazModulus.candidate_nongeneric_four_exp_barrier`. The statement does not use $e^{u}$.
--
--   **Novelty.** Not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.4(b). Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_conj_pair_four_exp_barrier (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by sorry

end DiazModulus
