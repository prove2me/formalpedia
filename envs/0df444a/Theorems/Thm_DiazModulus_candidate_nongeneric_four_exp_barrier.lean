-- Prove2me | Theorems.Thm_DiazModulus_candidate_nongeneric_four_exp_barrier
-- name    : DiazModulus.candidate_nongeneric_four_exp_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T20:37:15.688511+00:00
-- url     : https://prove2.me/theorems/024631c4-4d51-41d2-b346-2da1b253bb62
-- title:
--   For a candidate algebraic over ℚ(π), singular 2×2 matrices over ℚu + ℚū + ℚiπ have dependent rows or columns
-- statement:
--   **The barrier for non-generic candidates.**
--
--   Let $u$ be a candidate for Diaz's conjecture that is algebraic over $\mathbb{Q}[i\pi]$, and let $M$ be a $2\times2$ matrix whose entries are rational linear combinations of $u$, $\bar u$ and $i\pi$. If $\det M = 0$, then the rows of $M$ are $\mathbb{Q}$-linearly dependent or its columns are.
--
--   With `DiazModulus.generic_conj_pair_four_exp_barrier` this covers every candidate: a candidate is either algebraically independent of $\pi$ or algebraic over $\mathbb{Q}(\pi)$. So for every candidate the four exponentials conjecture, restricted to the logarithms the candidate certifies, is already a theorem. In the generic case this follows by algebra, and here by the four exponentials theorem in transcendence degree one. In fact a non-generic candidate with $\operatorname{Im} u \notin \mathbb{Q}\pi$ carries no rational quadratic relation among $u$, $\bar u$, $i\pi$ at all: these are $\mathbb{Q}$-linearly independent logarithms of algebraic numbers in a field of transcendence degree one, and Théorème 0.2 of D. Roy and M. Waldschmidt (Ann. Sci. École Norm. Sup. 30, 1997), the analogue of the present statement for an arbitrary quadric, excludes such a relation. (An earlier version of this text said that such candidates can carry relations such as $\operatorname{Re}(u^{2}) = \pi^{2}$; they cannot.) Vacuous if Diaz's conjecture holds.
--
--   **Novelty.** None: the statement is a direct consequence of the four exponentials theorem in transcendence degree one, which is the case $d = \ell = 2$ of Théorème 0.1 of D. Roy and M. Waldschmidt (Ann. Sci. École Norm. Sup. 30, 1997, p. 755); they note that this case was proved earlier, in an equivalent form, by W. D. Brownawell (J. Number Theory 6, 1974) and M. Waldschmidt (J. Number Theory 5, 1973). It is Proposition 5.5 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). The contribution of this node is the formal proof.
-- source:
--   Known: a direct consequence of the four exponentials theorem in transcendence degree one, which is the case d = ℓ = 2 of D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Théorème 0.1, p. 755, proved earlier in an equivalent form by W. D. Brownawell, J. Number Theory 6 (1974), 22–31, and M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Stated as Proposition 5.5 in Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_nongeneric_four_exp_barrier (u : ℂ) (hu : IsCandidate u)
    (halg : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) u)
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by sorry

end DiazModulus
