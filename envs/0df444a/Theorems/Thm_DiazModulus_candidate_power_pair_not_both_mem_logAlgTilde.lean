-- Prove2me | Theorems.Thm_DiazModulus_candidate_power_pair_not_both_mem_logAlgTilde
-- name    : DiazModulus.candidate_power_pair_not_both_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:09:36.923076+00:00
-- url     : https://prove2.me/theorems/3706795a-5cd8-46fe-a412-48bb68de49e7
-- title:
--   At a candidate u, with Roy's strong six exponentials theorem as hypothesis: for 4 ≤ k < l with l ∈ {k+1, k+2, 2k−1, 2k, 2k+1, 3k}, u^k and u^l are not both in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`) and $4 \le k < l$ with $l \in \{k + 1, k + 2, 2k - 1, 2k, 2k + 1, 3k\}$. Then $u^k$ and $u^l$ are not both in $\widetilde{\mathcal{L}}$. For example, no two consecutive powers $u^k, u^{k+1}$ with $k \ge 4$ are both in $\widetilde{\mathcal{L}}$. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** $\rho = |u|^2$ is algebraic and $u$ is transcendental (`DiazModulus.hermite_lindemann_holds`), so powers of $u$ with distinct integer exponents are $\overline{\mathbb{Q}}$-independent. By conjugation (`DiazModulus.logAlgTilde_conj_stable`), $u^n \in \widetilde{\mathcal{L}}$ gives $u^{-n} = \rho^{-n}\,\overline{u^n} \in \widetilde{\mathcal{L}}$, so $u^s \in \widetilde{\mathcal{L}}$ for $s \in \{0, \pm1, \pm k, \pm l\}$. In each case $x = (u^a)_{a \in A}$, $y = (u^b)_{b \in B}$ is a $2 \times 3$ configuration in $\widetilde{\mathcal{L}}$, against `hSSE`: $l = k + 1$: $A = \{0, 1\}$, $B = \{-1, 0, k\}$; $l = k + 2$: $\{0, 2\}$, $\{-1, k, -k - 2\}$; $l = 2k - 1$: $\{0, k - 1\}$, $\{1, -k, k\}$; $l = 2k$: $\{0, k\}$, $\{0, -k, k\}$; $l = 2k + 1$: $\{0, k + 1\}$, $\{-1, -k, k\}$; $l = 3k$: $\{0, 2k\}$, $\{-k, k, -3k\}$.
--
--   **Novelty.** Not asserted: each case is one substitution in Diaz (2007): $l = k + 1$ in Cor. 2(P)(1); $l = k + 2$, $2k - 1$, $2k + 1$ in Th. 7(1); $l = 2k$ and $3k$ in Cor. 5(1) and 5(2), with $\lambda = u^k$ and $\bar u^k = \rho^k u^{-k}$. Diaz does not state them at a candidate.
-- source:
--   Each case is one substitution in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391: Cor. 2(P)(1) (p. 381), Th. 7(1) (p. 390), Cor. 5(1)-(2) (p. 383). Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2) is carried as a hypothesis. Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_power_pair_not_both_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) (k l : ℕ) (hk : 4 ≤ k) (hkl : k < l)
    (hl : l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) :
    ¬ (u ^ k ∈ LogAlgTilde ∧ u ^ l ∈ LogAlgTilde) := by
  sorry

end DiazModulus
