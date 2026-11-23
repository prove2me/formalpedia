-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_sum_prj
-- name    : Formalism.HN.PlaceDecomposition.sum_prj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:10.040871+00:00
-- url     : https://prove2.me/theorems/1276731c-58f6-4432-b215-649237decb32
-- title:
--   Place Decomposition: sum prj
-- statement:
--   The Place Decomposition construction uses the sum prj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L165-L171

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

theorem Formalism.HN.PlaceDecomposition.sum_prj (w : EuclideanSpace ℝ (P × ι × Fin 2)) : ∑ v, prj v w = w := by sorry
