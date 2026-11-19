-- Prove2me | Theorems.Thm_Dense_holderWith_extend
-- name    : Dense.holderWith_extend
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:10:54.427294+00:00
-- url     : https://prove2.me/theorems/c6d1d6e7-d54c-4e52-91d6-40961dd79eb3
-- title:
--   holderWith extend
-- statement:
--   The source theorem `Dense.holderWith_extend` is extracted from `BrownianMotion.Auxiliary.Topology`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000


@[expose] public section

open Bornology Filter

open scoped NNReal ENNReal Topology

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [CompleteSpace Y]
    {C r : ℝ≥0} {s : Set X} {f : s → Y}

theorem Dense.holderWith_extend (hs : Dense s) (hf : HolderWith C r f) (hr : 0 < r) :
    HolderWith C r (hs.extend f) := by sorry
