-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_FinitePrinter_printsIn_of_prints
-- name    : CatalyticTreeEval.Contracts.FinitePrinter.printsIn_of_prints
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T06:26:37.954895+00:00
-- url     : https://prove2.me/theorems/7ed0ec04-8688-460f-97f9-83e3e2319de0
-- title:
--   Explicit native printer time bound from addressed workspace
-- statement:
--   Let M be a fixed native binary machine with s control states. If M prints a finite string y on input x, has empty catalyst and visits only the first b addressed work cells, then the same machine prints y within $$(s+1)(|x|+2)b2^b$$ transitions and the same workspace. For the mission printing predicate, b is the ceiling of its real workspace allowance. The statement charges the input-head and control information explicitly and allows arbitrarily long unreadable output histories. It supports the timed native access constructions needed by the main simulation.
-- source:
--   Infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, uniform printing and native access construction.

import Definitions.Def_CatalyticTreeEval_FinitePrinter

namespace CatalyticTreeEval.Contracts.FinitePrinter

theorem printsIn_of_prints (M : CatalyticTreeEval.Main.Machine) (input output : List Bool) (space : ℝ)
    (prints : CatalyticTreeEval.Main.Prints M input output space) :
    CatalyticTreeEval.Main.PrintsIn M input output space
      (CatalyticTreeEval.Contracts.FinitePrinter.configurationBound M input.length ⌈space⌉₊ : ℝ) := by
  sorry

end CatalyticTreeEval.Contracts.FinitePrinter
