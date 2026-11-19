-- Prove2me | Theorems.Thm_DiazModulus_qbar_linearIndependent_complex
-- name    : DiazModulus.qbar_linearIndependent_complex
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:33.486257+00:00
-- url     : https://prove2.me/theorems/23c6e61e-8ccf-4294-a191-d4f00ac23260
-- title:
--   Vectors of ℂᵐ with algebraic coordinates that are linearly independent over Q̄ are linearly independent over ℂ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $w_1, \dots, w_n \in \mathbb C^m$ be vectors with algebraic coordinates, linearly independent over $\overline{\mathbb Q}$. Then $w_1, \dots, w_n$ are linearly independent over $\mathbb C$.
-- source:
--   Classical linear algebra; a step of the proof of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.4 (2) (p. 185). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem qbar_linearIndependent_complex {n m : ℕ} (w : Fin n → Fin m → ℂ)
    (hw : ∀ a i, w a i ∈ Qbar) (hind : LinearIndependent (↥Qbar) w) :
    LinearIndependent ℂ w := by
  sorry

end DiazModulus
