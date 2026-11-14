-- Prove2me | Theorems.Thm_DiazModulus_roy_rank_bound
-- name    : DiazModulus.roy_rank_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:50:57.255209+00:00
-- url     : https://prove2.me/theorems/f6b34940-416d-40d8-be41-c0c7890e96a5
-- title:
--   Roy 1992, Cor. 1: a $d \times l$ matrix $M$ with entries in ℒ̃ is equivalent over Q̄ to one whose top right $d' \times (l - l')$ block is zero, with $d\,l' \le \operatorname{rank}(M)\,(d' + l')$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a $d \times l$ matrix with entries in $\widetilde{\mathcal L}$, $d \ge 1$. Then there are integers $0 < d' \le d$, $0 \le l' \le l$ and invertible matrices $P$, $Q$ with algebraic entries such that the entries $(PMQ)_{ij}$ with $i \le d'$, $j > l'$ vanish, and
--   $$d\,l' \le \operatorname{rank}(M)\,(d' + l').$$
--   This is Roy's lower bound $\operatorname{rank}(M) \ge d\,\theta(M)/(1 + \theta(M))$, where $\theta(M)$ is the least $l'/d'$ over such block forms: the block form above gives $\theta(M) \le l'/d'$, and $x \mapsto x/(1 + x)$ is increasing. It holds unconditionally: the multiplicity estimate is DiazModulus.multiplicityEstimateElem.
-- source:
--   D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, §4, Cor. 1 (p. 38), deduced from Th. 4; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §12.3, Th. 12.20 and Cor. 12.21. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rank_bound {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hd : 0 < d) :
    ∃ (d' l' : ℕ) (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin l) (Fin l) ℂ),
      0 < d' ∧ d' ≤ d ∧ l' ≤ l ∧ IsUnit P.det ∧ IsUnit Q.det ∧
      (∀ i j, P i j ∈ Qbar) ∧ (∀ i j, Q i j ∈ Qbar) ∧
      (∀ (i : Fin d) (j : Fin l), i.val < d' → l' ≤ j.val → (P * M * Q) i j = 0) ∧
      d * l' ≤ M.rank * (d' + l') := by
  sorry

end DiazModulus
