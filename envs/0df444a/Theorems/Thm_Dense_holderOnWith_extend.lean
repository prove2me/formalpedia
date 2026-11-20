-- Prove2me | Theorems.Thm_Dense_holderOnWith_extend
-- name    : Dense.holderOnWith_extend
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:41:08.14089+00:00
-- url     : https://prove2.me/theorems/8a9057ed-919e-4f89-a99c-e97a1cdf2baa
-- title:
--   holderOnWith extend
-- statement:
--   The source theorem `Dense.holderOnWith_extend` is extracted from `BrownianMotion.Continuity.KolmogorovChentsov`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

theorem Dense.holderOnWith_extend {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [CompleteSpace Y] {C r : ℝ≥0} {s : Set X} {f : s → Y} {U : Set X} (hU : IsOpen U) (hs : Dense s)
    (hf : HolderOnWith C r f {x | ↑x ∈ U}) (hr : 0 < r) :
    HolderOnWith C r (hs.extend f) U := by sorry
