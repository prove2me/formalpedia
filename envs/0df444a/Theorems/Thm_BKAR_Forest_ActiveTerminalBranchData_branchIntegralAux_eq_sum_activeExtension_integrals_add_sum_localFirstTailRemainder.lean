-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:17.254814+00:00
-- url     : https://prove2.me/theorems/631402f7-e26e-4a74-b357-c49b9e58f343
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum active Extension integrals add sum local First Tail Remainder
-- statement:
--   The selected terminal branch sum at a local recursion node is the one-step
--   active-extension remainder plus the sum of the local first-tail errors.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L66-L84
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L66-L84

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) +
        Finset.sum F.activeEdges.attach
          (fun e => data.localFirstTailRemainder e top u es ρ) := by sorry
