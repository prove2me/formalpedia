-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_mem_placePart
-- name    : Formalism.HN.PlaceDecomposition.mem_placePart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:20.558566+00:00
-- url     : https://prove2.me/theorems/7d586bd3-dbb5-4282-8b6a-bef8ea6dc01d
-- title:
--   Place Decomposition: mem place Part
-- statement:
--   The Place Decomposition construction uses the mem place Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L145-L150

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]

theorem Formalism.HN.PlaceDecomposition.mem_placePart (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) :
    w ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → w p = 0 := by sorry
