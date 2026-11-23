-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_mem
-- name    : Formalism.HN.PlaceDecomposition.prj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:10.879993+00:00
-- url     : https://prove2.me/theorems/2007f72d-8bc0-4678-91b5-09ea3f82e5f2
-- title:
--   Place Decomposition: prj mem
-- statement:
--   The Place Decomposition construction uses the prj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L152-L155

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

theorem Formalism.HN.PlaceDecomposition.prj_mem (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) : prj v w ∈ placePart v := by sorry
