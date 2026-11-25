-- Prove2me | Theorems.Thm_DetDLP_primitive_machine_trace_and_space_foundations
-- name    : DetDLP.primitive_machine_trace_and_space_foundations
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:28:57.833265+00:00
-- url     : https://prove2.me/theorems/0db56b31-e89b-4345-8224-0be2780d2c31
-- title:
--   Multitape PrimitiveMachine Determinism, Unique Halting, and Space-Time Execution Laws
-- statement:
--   Establishes the fundamental execution, determinism, and space-time complexity laws for deterministic multitape `PrimitiveMachine` computations (`Trace`, `locatedInit`, `locatedStep`, `visitedSpace`, and `RunsWithin`):
--
--   1. **Determinism and unique halting:** `Trace step` is deterministic at fixed step count and has a unique halting step count $time_1 = time_2$ and unique final configuration $final_1 = final_2$;
--   2. **Initial and step-k space bounds:** for every machine $M$, input $x$, step $k$, and reachable configuration $c$, $\mathrm{visitedSpace}(\mathrm{locatedInit}(M, x)) \le |x| + M.\mathrm{tapeCount}$ and $\mathrm{visitedSpace}(c) \le |x| + M.\mathrm{tapeCount} + k$;
--   3. **Automatic Space Certificate and budget monotonicity for `RunsWithin`:** any halting trace of length $time \le \tau$ with $|x| + M.\mathrm{tapeCount} + time \le \sigma$ automatically satisfies `RunsWithin M out x y τ σ`, and `RunsWithin` is monotone in $(\tau, \sigma)$;
--   4. **Explicit Halting `PrimitiveMachine` Construction:** constructs a concrete `PrimitiveMachine` halting in $1$ step with space $\le |x| + 2$ on every input $x$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 1.2 & Section 2.2 Computational Model (pp. 4, 7–8)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Fundamental execution, determinism, and space-time complexity laws for `PrimitiveMachine`,
`Trace`, `locatedStep`, `visitedSpace`, and `RunsWithin`:
(1) Step-count determinism of `Trace`.
(2) Unique halting step and unique final configuration of `Trace` across all step counts.
(3) Unique halting time and final configuration for any `PrimitiveMachine` execution from `locatedInit`.
(4) Initial configuration space bound: `visitedSpace (locatedInit M input) ≤ input.length + M.tapeCount`.
(5) Space-Time Bounding Theorem: at step `k`, `visitedSpace c ≤ input.length + M.tapeCount + k`.
(6) Automatic Space Certificate for `RunsWithin`: any halting run of length `time ≤ τ` with
    `input.length + M.tapeCount + time ≤ σ` automatically satisfies `RunsWithin M out input output τ σ`.
(7) Monotonicity of `RunsWithin` in time and space budgets `(τ, σ)`.
(8) Explicit Halting `PrimitiveMachine` Construction: there exists a concrete `PrimitiveMachine`
    halting with `RunsWithin M out input input 1 (input.length + 2)` on every input. -/
theorem primitive_machine_trace_and_space_foundations :
    (∀ {α : Type} (step : α → Option α) (k : ℕ) (a b₁ b₂ : α),
      Trace step k a b₁ → Trace step k a b₂ → b₁ = b₂) ∧
    (∀ {α : Type} (step : α → Option α) (k₁ k₂ : ℕ) (a b₁ b₂ : α),
      Trace step k₁ a b₁ → step b₁ = none →
      Trace step k₂ a b₂ → step b₂ = none →
      k₁ = k₂ ∧ b₁ = b₂) ∧
    (∀ (M : PrimitiveMachine) (time₁ time₂ : ℕ) (input : List Bool)
        (final₁ final₂ : LocatedCfg M) (b₁ b₂ : Bool),
      Trace (locatedStep M) time₁ (locatedInit M input) final₁ →
      final₁.config.state = Sum.inl b₁ →
      Trace (locatedStep M) time₂ (locatedInit M input) final₂ →
      final₂.config.state = Sum.inl b₂ →
      time₁ = time₂ ∧ final₁ = final₂) ∧
    (∀ (M : PrimitiveMachine) (input : List Bool),
      visitedSpace (locatedInit M input) ≤ input.length + M.tapeCount) ∧
    (∀ (M : PrimitiveMachine) (input : List Bool) (k : ℕ) (c : LocatedCfg M),
      Trace (locatedStep M) k (locatedInit M input) c →
      visitedSpace c ≤ input.length + M.tapeCount + k) ∧
    (∀ (M : PrimitiveMachine) (out : Fin M.tapeCount) (input output : List Bool)
        (τ σ : ℝ) (time : ℕ) (final : LocatedCfg M) (b : Bool),
      Trace (locatedStep M) time (locatedInit M input) final →
      final.config.state = Sum.inl b →
      final.config.tapes out = Turing.Tape.mk₁ (output.map some) →
      (time : ℝ) ≤ τ →
      ((input.length + M.tapeCount + time : ℕ) : ℝ) ≤ σ →
      RunsWithin M out input output τ σ) ∧
    (∀ (M : PrimitiveMachine) (out : Fin M.tapeCount) (input output : List Bool)
        (τ₁ σ₁ τ₂ σ₂ : ℝ),
      RunsWithin M out input output τ₁ σ₁ → τ₁ ≤ τ₂ → σ₁ ≤ σ₂ →
      RunsWithin M out input output τ₂ σ₂) ∧
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount),
      ∀ (input : List Bool),
        RunsWithin M out input input 1 ((input.length + 2 : ℕ) : ℝ)) := by
  sorry

end DetDLP
