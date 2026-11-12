-- Prove2me | Theorems.Thm_Erdos970_Complex_Hadamard_exists_entire_nonzero_hadamardQuotient_jb247
-- name    : Erdos970.Complex.Hadamard.exists_entire_nonzero_hadamardQuotient_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:44:52.944585+00:00
-- url     : https://prove2.me/theorems/c8c37faf-b56e-4abe-bfcb-2ce3d5db2d50
-- title:
--   Erdos970.Complex.Hadamard.exists_entire_nonzero_hadamardQuotient_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970.Complex.Hadamard`, with `open _root_.Complex`, `open _root_.Filter Topology _root_.Set Complex`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_entire_nonzero_hadamardQuotient_jb247
--       (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
--       (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
--         ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
--       ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
--         H z * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.Complex.Hadamard.divisorCanonicalProduct`, `Erdos970.Complex.Hadamard.divisorZeroIndex₀` and `Erdos970.Complex.Hadamard.divisorZeroIndex₀_val` (definitions bundle `OAIQ247J000` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

open _root_.Filter Topology _root_.Set Complex

open scoped BigOperators Topology

theorem exists_entire_nonzero_hadamardQuotient_jb247
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  sorry

end Complex.Hadamard
end Erdos970
end
