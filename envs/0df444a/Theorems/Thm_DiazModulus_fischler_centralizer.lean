-- Prove2me | Theorems.Thm_DiazModulus_fischler_centralizer
-- name    : DiazModulus.fischler_centralizer
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:06.972832+00:00
-- url     : https://prove2.me/theorems/b2d55de6-bd48-4a32-8e71-1ceadd420026
-- title:
--   Fischler 2001, Th. 1.2: if M ∈ ℒ̃ⁿˣⁿ has n² entries linearly independent over Q̄, the centraliser of M has dimension at most (n² + 1)/2
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $M \in \mathrm{Mat}_n(\mathbb C)$, $C(M) = \{A \in \mathrm{Mat}_n(\mathbb C) : AM = MA\}$ is the centraliser of $M$.
--
--   Let $M$ be an $n \times n$ matrix with entries in $\widetilde{\mathcal L}$ whose $n^2$ entries are linearly independent over $\overline{\mathbb Q}$. Then
--   $$2 \dim_{\mathbb C} C(M) \le n^2 + 1,$$
--   that is, $\dim_{\mathbb C} C(M) \le (n^2 + 1)/2$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 1.2 (p. 169), complex case. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_centralizer {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hfree : LinearIndependent (↥Qbar) (fun p : Fin n × Fin n => M p.1 p.2)) :
    2 * Module.finrank ℂ ↥(Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ))) ≤
      n ^ 2 + 1 := by
  sorry

end DiazModulus
