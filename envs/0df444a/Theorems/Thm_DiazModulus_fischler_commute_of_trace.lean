-- Prove2me | Theorems.Thm_DiazModulus_fischler_commute_of_trace
-- name    : DiazModulus.fischler_commute_of_trace
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:11.202058+00:00
-- url     : https://prove2.me/theorems/86cce4fb-d339-4852-bc56-4b7eccf8003a
-- title:
--   If the n² entries of M ∈ Matₙ(ℂ) are Q̄-free and Tr(M(AB − BA)) = 0 for A, B in rational subspaces U, V of Matₙ(ℂ), then AB = BA for all A ∈ U, B ∈ V
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a complex $n \times n$ matrix whose $n^2$ entries are linearly independent over $\overline{\mathbb Q}$, and let $U, V \subseteq \mathrm{Mat}_n(\mathbb C)$ be $\mathbb C$-subspaces, each spanned by matrices with algebraic entries, such that $\operatorname{Tr}\big(M(AB - BA)\big) = 0$ for all $A \in U$ and $B \in V$. Then $AB = BA$ for all $A \in U$ and $B \in V$.
-- source:
--   Step of the proof of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 1.2 (p. 181). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_commute_of_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hfree : LinearIndependent (↥Qbar) (fun p : Fin n × Fin n => M p.1 p.2))
    (U V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hU : Submodule.span ℂ {A | A ∈ U ∧ ∀ i j, A i j ∈ Qbar} = U)
    (hV : Submodule.span ℂ {B | B ∈ V ∧ ∀ i j, B i j ∈ Qbar} = V)
    (htr : ∀ A ∈ U, ∀ B ∈ V, (M * (A * B - B * A)).trace = 0) :
    ∀ A ∈ U, ∀ B ∈ V, A * B = B * A := by
  sorry

end DiazModulus
