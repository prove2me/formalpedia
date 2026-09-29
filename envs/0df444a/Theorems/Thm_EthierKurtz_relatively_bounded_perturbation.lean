-- Prove2me | Theorems.Thm_EthierKurtz_relatively_bounded_perturbation
-- name    : EthierKurtz.relatively_bounded_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:43:25.642987+00:00
-- url     : https://prove2.me/theorems/d41e299f-2fea-4685-a45e-b20c0508a65c
-- title:
--   Theorem 7.1 — relatively bounded dissipative perturbations
-- statement:
--   If the closure of A generates a strongly continuous contraction semigroup, B is dissipative with a domain containing that of A, and B has relative A-bound below one, then the closure of A+B generates such a semigroup and equals the sum of the graph closures.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, Section 7, Theorem 7.1, printed p. 37 (PDF p. 46).

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_IsInfinitesimalGenerator
import Definitions.Def_EthierKurtz_unboundedOperatorGraph
import Definitions.Def_EthierKurtz_operatorGraphSum

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Relatively bounded dissipative perturbation theorem. The closure of A
is represented by its entire graph, not by an assumed closed original A.
The existential graph representation in the conclusion asserts single-valuedness
of the closure of A+B. The final equality includes the full domain assertion. -/
theorem relatively_bounded_perturbation [CompleteSpace E]
    (DA DB : Submodule ℝ E) (A : DA →ₗ[ℝ] E) (B : DB →ₗ[ℝ] E)
    (hdom : DA ≤ DB)
    (hA : ∃ (Dbar : Submodule ℝ E) (Abar : Dbar →ₗ[ℝ] E)
        (T : ℝ → E →L[ℝ] E),
      unboundedOperatorGraph Dbar Abar = closure (unboundedOperatorGraph DA A) ∧
      IsStronglyContinuousContractionSemigroup T ∧
      IsInfinitesimalGenerator Dbar Abar T)
    (hB : ∀ r : ℝ, 0 < r → ∀ x : DB,
      r * ‖(x : E)‖ ≤ ‖r • (x : E) - B x‖)
    (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hbound : ∀ x : DA,
      ‖B (Submodule.inclusion hdom x)‖ ≤ α * ‖A x‖ + β * ‖(x : E)‖) :
    ∃ (DS : Submodule ℝ E) (S : DS →ₗ[ℝ] E) (T : ℝ → E →L[ℝ] E),
      unboundedOperatorGraph DS S =
        closure (operatorGraphSum (unboundedOperatorGraph DA A)
          (unboundedOperatorGraph DB B)) ∧
      IsStronglyContinuousContractionSemigroup T ∧
      IsInfinitesimalGenerator DS S T ∧
      closure (operatorGraphSum (unboundedOperatorGraph DA A)
        (unboundedOperatorGraph DB B)) =
        operatorGraphSum (closure (unboundedOperatorGraph DA A))
          (closure (unboundedOperatorGraph DB B)) := by sorry
