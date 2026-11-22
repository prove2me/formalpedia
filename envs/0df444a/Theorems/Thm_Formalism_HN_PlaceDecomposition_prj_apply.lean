-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_apply
-- name    : Formalism.HN.PlaceDecomposition.prj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:26:45.772746+00:00
-- url     : https://prove2.me/theorems/28a75edd-f326-4d35-a614-ed8d9bfc0435
-- title:
--   Place Decomposition: prj apply
-- statement:
--   The Place Decomposition construction uses the prj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L132-L133

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

theorem Formalism.HN.PlaceDecomposition.prj_apply (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    prj v w p = if p.1 = v then w p else 0 := by sorry
