-- Prove2me | Theorems.Thm_DetDLP_m89_resettable_machine
-- name    : DetDLP.m89_resettable_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T01:58:01.73886+00:00
-- url     : https://prove2.me/theorems/c7a7702b-2acd-4a1c-a5b6-aa71f5888dcb
-- title:
--   Resettable Single-Pass Tape-Clearing Wrapper for PrimitiveMachines
-- statement:
--   For any `PrimitiveMachine` $A$ and designated output tape `outA : Fin A.tapeCount`, there exists a single-pass wrapper `PrimitiveMachine` $R$ and constant $C \ge 1$ such that whenever $A$ computes `output` from `input` within time $\tau \ge 0$ and space $\sigma \ge 0$, $R$ halts within $C(\tau + \sigma + 1)$ steps with `output` left on `R.inputTape`, all other tapes empty `Tape.mk₁ []`, all heads reset to position `0`, and all tape bounds contained in $[-B, B]$ for $B \le C(\sigma + 1)$.
-- source:
--   Helper lemma for Milestones #8 and #9 (Universal multi-round oracle loop)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Universal resettable wrapper for any deterministic `PrimitiveMachine` `A`:
produces a uniform `PrimitiveMachine` `R` whose output tape is `R.inputTape` such that
whenever `RunsWithin A outA input output τ σ`, `R` halts from `locatedInit R input` with
`output` on `R.inputTape`, all other tapes completely blank, all heads returned to cell `0`,
step count `≤ C * (τ + σ + 1)`, and every visited cell on every tape inside `[-B, B]` for a
natural bound `B ≤ C * (σ + 1)`. -/
theorem m89_resettable_machine (A : PrimitiveMachine) (outA : Fin A.tapeCount) :
    ∃ (R : PrimitiveMachine) (C : ℕ),
      1 ≤ C ∧
      ∀ (input output : List Bool) (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
        RunsWithin A outA input output τ σ →
        ∃ (n B : ℕ) (final : LocatedCfg R),
          Computation.Trace (locatedStep R) n (locatedInit R input) final ∧
          (∃ b : Bool, final.config.state = .inl b) ∧
          final.config.tapes R.inputTape = Turing.Tape.mk₁ (output.map some) ∧
          (∀ j : Fin R.tapeCount, j ≠ R.inputTape → final.config.tapes j = Turing.Tape.mk₁ []) ∧
          (∀ j : Fin R.tapeCount, final.position j = 0) ∧
          (n : ℝ) ≤ (C : ℝ) * (τ + σ + 1) ∧
          (B : ℝ) ≤ (C : ℝ) * (σ + 1) ∧
          (∀ j : Fin R.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ)) := by sorry

end DetDLP
