-- Prove2me | Theorems.Thm_DiazModulus_fischler_prop_5_5
-- name    : DiazModulus.fischler_prop_5_5
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:21.798028+00:00
-- url     : https://prove2.me/theorems/2a46317f-a2a6-49f1-9b79-b94bb464beea
-- title:
--   Fischler's Proposition 5.5 in rational form: if M ∈ ℒ̃ⁿˣⁿ and 2 dim C(M) ≥ n² + 2, there are rational U, V ⊆ Matₙ(ℂ) with dim U + dim V ≥ n² + 2 and Tr(M[A, B]) = 0 on U × V
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $M \in \mathrm{Mat}_n(\mathbb C)$, $C(M) = \{A \in \mathrm{Mat}_n(\mathbb C) : AM = MA\}$ is the centraliser of $M$.
--
--   Let $M$ be an $n \times n$ matrix with entries in $\widetilde{\mathcal L}$ such that $2 \dim_{\mathbb C} C(M) \ge n^2 + 2$. Then there are $\mathbb C$-subspaces $U, V \subseteq \mathrm{Mat}_n(\mathbb C)$, each spanned by matrices with algebraic entries, such that $\dim U + \dim V \ge n^2 + 2$ and
--   $$\operatorname{Tr}\big(M(AB - BA)\big) = 0 \quad\text{for all } A \in U,\ B \in V.$$
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Prop. 5.5 (pp. 181–183), in rational form; a step of the proof of Th. 1.2 (p. 169). Roy's Corollary 1 (Roy 1992, Cor. 1; DALAG, Th. 12.20, p. 435), proved on the platform as DiazModulus.roy_rank_bound, is applied to ad M on the trace-zero matrices written in coordinates, in place of Fischler's Cor. 2.2 (pp. 170–171), so that U and V are spanned by explicit algebraic matrices. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_prop_5_5 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hC : n ^ 2 + 2 ≤ 2 * Module.finrank ℂ ↥(Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ)))) :
    ∃ U V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
      Submodule.span ℂ {A | A ∈ U ∧ ∀ i j, A i j ∈ Qbar} = U ∧
      Submodule.span ℂ {B | B ∈ V ∧ ∀ i j, B i j ∈ Qbar} = V ∧
      n ^ 2 + 2 ≤ Module.finrank ℂ ↥U + Module.finrank ℂ ↥V ∧
      ∀ A ∈ U, ∀ B ∈ V, (M * (A * B - B * A)).trace = 0 := by
  sorry

end DiazModulus
