-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_of_mem
-- name    : Formalism.HN.PlaceDecomposition.prj_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:16.388572+00:00
-- url     : https://prove2.me/theorems/0a35e8a6-5d4c-4d53-b39d-3f861fb24131
-- title:
--   Place Decomposition: prj of mem
-- statement:
--   The Place Decomposition construction uses the prj of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L157-L163

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

theorem Formalism.HN.PlaceDecomposition.prj_of_mem (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (hw : w ∈ placePart v) :
    prj v w = w := by sorry
