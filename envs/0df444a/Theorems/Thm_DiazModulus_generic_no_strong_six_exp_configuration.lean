-- Prove2me | Theorems.Thm_DiazModulus_generic_no_strong_six_exp_configuration
-- name    : DiazModulus.generic_no_strong_six_exp_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T07:01:19.972985+00:00
-- url     : https://prove2.me/theorems/6f340972-bef6-46ba-bb8d-61ba0753e4a9
-- title:
--   For u algebraically independent of π on a circle of algebraic radius, no configuration of the strong six exponentials theorem lies over Q̄ + Q̄u + Q̄ū + Q̄iπ
-- statement:
--   **The strong six exponentials theorem cannot refute a generic candidate, even with $i\pi$.**
--
--   Let $u \neq 0$ with $|u|^{2}$ algebraic, and suppose that $u$ and $i\pi$ are algebraically independent over $\overline{\mathbb{Q}}$. Then there are no $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, such that all six products $x_i y_j$ lie in the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, i\pi$.
--
--   Roy's strong six exponentials theorem says that for such $x$ and $y$ one of the six products lies outside $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\mathcal{L}$. A candidate for Diaz's conjecture certifies $u$, $\bar u$ and $i\pi$ as logarithms of algebraic numbers, and its algebraic modulus makes the constant available. This node shows that these four dimensions never hold a configuration, so the theorem gives nothing against a generic candidate. It extends `DiazModulus.sixExponentials_cannot_refute_candidate` from $1, u, \bar u$ to $1, u, \bar u, i\pi$, where counting dimensions no longer suffices: the proof uses that every quadratic relation among $1, u, \bar u, i\pi$ is a multiple of the norm (`DiazModulus.generic_quadratic_relation_is_norm`). G. Diaz (2007) remarks that the strong six exponentials theorem has produced no example of a $\lambda$ with $|\lambda| \notin \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\mathcal{L}$; on a generic candidate's own data, this node is one reason.
--
--   **Novelty.** None claimed. Elementary given the norm lemma; not found in Diaz (2007), Waldschmidt (2005) or Roy–Waldschmidt (1997).
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.6(c). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: D. Roy, J. Number Theory 41 (1992) 22–47; G. Diaz, J. Théor. Nombres Bordeaux 19 (2007) 373–391.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_no_strong_six_exp_configuration (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
  sorry

end DiazModulus
