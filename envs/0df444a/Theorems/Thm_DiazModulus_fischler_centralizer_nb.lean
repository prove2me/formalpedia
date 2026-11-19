-- Prove2me | Theorems.Thm_DiazModulus_fischler_centralizer_nb
-- name    : DiazModulus.fischler_centralizer_nb
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:10.20111+00:00
-- url     : https://prove2.me/theorems/17475831-cba3-4d8c-ace9-229add7e52f5
-- title:
--   Fischler 2001, N.B. after Prop. 5.5: if M ∈ ℒ̃ⁿˣⁿ and no hyperplane of Matₙ(ℂ) defined over Q̄ contains both M and the identity, then dim C(M) ≤ (n² + 1)/2
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $M \in \mathrm{Mat}_n(\mathbb C)$, $C(M) = \{A \in \mathrm{Mat}_n(\mathbb C) : AM = MA\}$ is the centraliser of $M$.
--
--   Let $M$ be an $n \times n$ matrix with entries in $\widetilde{\mathcal L}$, and assume that no hyperplane of $\mathrm{Mat}_n(\mathbb C)$ defined over $\overline{\mathbb Q}$ contains both $M$ and the identity matrix: if $c = (c_{ij})$ is an $n \times n$ matrix with algebraic entries such that $\sum_{i,j} c_{ij} M_{ij} = 0$ and $\sum_i c_{ii} = 0$, then $c = 0$. Then
--   $$2 \dim_{\mathbb C} C(M) \le n^2 + 1.$$
--   The hypothesis holds when the $n^2$ entries of $M$ are linearly independent over $\overline{\mathbb Q}$, so this implies Fischler's Theorem 1.2, complex case (DiazModulus.fischler_centralizer).
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, N.B. after Prop. 5.5 (p. 183): Th. 1.2 (p. 169), complex case, still holds when the hypothesis that the n² entries of M are Q̄-free is replaced by: no hyperplane of Matₙ(ℂ) defined over Q̄ contains both M and the identity. Hyperplanes are vector hyperplanes (convention of p. 169), and one defined over Q̄ is the kernel of a non-zero linear form with algebraic coefficients (p. 170). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The N.B. has no separate proof: the printed proof of Th. 1.2 (pp. 181–183) uses the freeness only to show that algebraic A, B with Tr(M(AB − BA)) = 0 commute, and the hypothesis gives that: when AB − BA ≠ 0, the kernel of N ↦ Tr(N(AB − BA)) is a hyperplane defined over Q̄ that contains M and the identity. Proved from DiazModulus.fischler_prop_5_5 and DiazModulus.remond_commuting_subspaces. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_centralizer_nb {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hhyp : ∀ c : Matrix (Fin n) (Fin n) ℂ, (∀ i j, c i j ∈ Qbar) →
      ∑ i, ∑ j, c i j * M i j = 0 → ∑ i, c i i = 0 → c = 0) :
    2 * Module.finrank ℂ ↥(Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ))) ≤
      n ^ 2 + 1 := by
  sorry

end DiazModulus
