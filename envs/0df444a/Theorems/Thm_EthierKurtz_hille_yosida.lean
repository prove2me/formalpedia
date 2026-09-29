-- Prove2me | Theorems.Thm_EthierKurtz_hille_yosida
-- name    : EthierKurtz.hille_yosida
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:42:43.71515+00:00
-- url     : https://prove2.me/theorems/d28fa1e3-f0eb-4e33-a8c1-f7cb47944c36
-- title:
--   Theorem 2.6 — Hille–Yosida characterization
-- statement:
--   A linear operator on a real Banach space generates a strongly continuous contraction semigroup if and only if its domain is dense, it is dissipative, and the range of one positive resolvent parameter is the whole space.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, Section 2, Theorem 2.6, printed p. 13 (PDF p. 22).

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_IsInfinitesimalGenerator

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hille--Yosida characterization, Chapter 1, Theorem 2.6.
The three conditions are dense domain, dissipativity, and full range of
`λ I - A` for at least one positive real `λ`. No boundedness or closedness
of `A` is assumed. -/
theorem hille_yosida [CompleteSpace E] (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) :
    (∃ T : ℝ → E →L[ℝ] E,
      IsStronglyContinuousContractionSemigroup T ∧ IsInfinitesimalGenerator D A T) ↔
    Dense (D : Set E) ∧
      (∀ r : ℝ, 0 < r → ∀ x : D, r * ‖(x : E)‖ ≤ ‖r • (x : E) - A x‖) ∧
      (∃ r : ℝ, 0 < r ∧ Function.Surjective (fun x : D => r • (x : E) - A x)) := by sorry
