-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_theorem_4_1_a
-- name    : ChenSimchiLevi.General.theorem_4_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:11:10.945641+00:00
-- url     : https://prove2.me/theorems/f86c0241-30e3-4c5b-b5d4-20f69ec109e1
-- title:
--   Theorem 4.1(a): polynomial growth of profit and value
-- statement:
--   Under Assumptions 1–5, for each $t=1,\ldots,T$, the one-period profit $g_t(y,d)$, uniformly over admissible expected demand $d$, and the profit-to-go $v_t(x)$ grow at most on the scale $1+|y|^\rho$ and $1+|x|^\rho$, respectively:
--   $$|g_t(y,d)|\le C_t(1+|y|^\rho),\qquad |v_t(x)|\le C'_t(1+|x|^\rho).$$
--   The continuation expectation appearing in $g_t$ is finite at every admissible decision. These bounds support the later continuity and symmetric concavity assertions.
--
--   **Formalization Note** The paper writes $O(|y|^\rho)$; the displayed bounds give an explicit constant and use $1+|y|^\rho$ to cover values near zero. Integrability of the continuation term is stated explicitly to exclude the zero default of a nonintegrable Lean integral.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, Theorem 4.1(a)

import Definitions.Def_ChenSimchiLevi_General_Model

set_option autoImplicit false

namespace ChenSimchiLevi.General

open MeasureTheory

/-- Theorem 4.1(a), p. 891, including finiteness of the continuation expectation. -/
theorem theorem_4_1_a (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (∃ C : ℝ, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        |M.g t y d| ≤ C * (1 + |y| ^ M.ρ)) ∧
      (∃ C : ℝ, ∀ x, |M.v t x| ≤ C * (1 + |x| ^ M.ρ)) ∧
      (∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        Integrable (fun ε : ℝ × ℝ => M.v (t + 1) (y - ε.1 * d - ε.2)) (M.μ t)) := by sorry

end ChenSimchiLevi.General
