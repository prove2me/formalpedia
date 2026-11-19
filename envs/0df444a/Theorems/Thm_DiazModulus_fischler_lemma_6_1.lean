-- Prove2me | Theorems.Thm_DiazModulus_fischler_lemma_6_1
-- name    : DiazModulus.fischler_lemma_6_1
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:13.179055+00:00
-- url     : https://prove2.me/theorems/1b85623e-daf9-4904-a8e3-7aaa8141b30c
-- title:
--   Fischler 2001, Lemma 6.1: if λ₁, …, λ_q are non-zero elements of ℒ̃ in geometric progression with transcendental ratio, then q ≤ 3
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\lambda_1, \dots, \lambda_q$ be non-zero elements of $\widetilde{\mathcal L}$ in geometric progression with ratio $t$, that is, $\lambda_{j+1} = t\lambda_j$ for $1 \le j < q$, and assume that $t$ is transcendental. Then $q \le 3$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The printed proof applies Th. 2.3 (Roy 1992, Cor. 2) to the 2 × (q − 1) matrix of consecutive terms; here Roy's strong six exponentials theorem in product form (DiazModulus.strong_six_exponentials_unconditional) is applied to its 2 × 3 corner. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_lemma_6_1 {q : ℕ} (lam : Fin q → ℂ) (t : ℂ)
    (hmem : ∀ j, lam j ∈ LogAlgTilde) (hne : ∀ j, lam j ≠ 0)
    (hgeo : ∀ i j : Fin q, i.val + 1 = j.val → lam j = t * lam i)
    (ht : Transcendental ℚ t) : q ≤ 3 := by
  sorry

end DiazModulus
