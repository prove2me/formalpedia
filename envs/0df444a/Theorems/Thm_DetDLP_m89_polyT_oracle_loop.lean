-- Prove2me | Theorems.Thm_DetDLP_m89_polyT_oracle_loop
-- name    : DetDLP.m89_polyT_oracle_loop
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T02:49:42.555959+00:00
-- url     : https://prove2.me/theorems/15bf7181-aece-4aba-8d66-20f2e2e3e713
-- title:
--   Universal Multi-Round PolyT Oracle-Loop Compiler for PrimitiveMachines
-- statement:
--   Given any polynomial-time function `step : List Bool -> List Bool` (`Groundwork.PolyT step`) and an arbitrary `PrimitiveMachine` oracle $O$ with output tape `outO`, there exists a single uniform `PrimitiveMachine` $M$ and constant $K \ge 1$ executing multi-round interactive loops between `step` and $O$ with full tape-space reuse across calls.
-- source:
--   Helper lemma for Milestones #8 and #9 (Factor-splitting driver and Stage II orchestration)

import Mathlib
import Definitions.Def_DetDLP_Machine
import Definitions.Def_ToTuring_PolyT

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Universal multi-round oracle-loop compiler: given any polynomial-time step function
`step : List Bool → List Bool` (`Groundwork.PolyT step`) and any arbitrary oracle
`PrimitiveMachine` `O` with output tape `outO`, there exists a single uniform
`PrimitiveMachine` `M` executing arbitrary-length interactive loops between `step` and `O`
with full tape-space reuse across calls. -/
theorem m89_polyT_oracle_loop
    (step : List Bool → List Bool) (hstep : Groundwork.PolyT step)
    (O : PrimitiveMachine) (outO : Fin O.tapeCount) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      1 ≤ K ∧
      ∀ (τO σO : ℝ), 0 ≤ τO → 0 ≤ σO →
        let pairWord : List Bool → List Bool → List Bool := fun x y =>
          x.flatMap (fun b => [true, b]) ++ [false] ++ y
        let loopRuns : ℕ → List Bool → List Bool → List Bool → ℕ → Prop :=
          Nat.rec (motive := fun _ => List Bool → List Bool → List Bool → ℕ → Prop)
            (fun _ _ _ _ => False)
            (fun _ prev st ans outW maxLen =>
              (step (pairWord st ans) = true :: outW ∧
                (pairWord st ans).length ≤ maxLen ∧ outW.length ≤ maxLen) ∨
              (∃ st' q ans',
                step (pairWord st ans) = false :: pairWord st' q ∧
                (pairWord st ans).length ≤ maxLen ∧
                (pairWord st' q).length ≤ maxLen ∧
                ans'.length ≤ maxLen ∧
                RunsWithin O outO q ans' τO σO ∧
                prev st' ans' outW maxLen))
        ∀ (rounds maxLen : ℕ) (input output : List Bool),
          1 ≤ rounds →
          loopRuns rounds input [] output maxLen →
          RunsWithin M out input output
            ((rounds : ℝ) * (polyBound K maxLen + (K : ℝ) * (τO + σO + 1)))
            (polyBound K maxLen + (K : ℝ) * (σO + 1)) := by sorry

end DetDLP
