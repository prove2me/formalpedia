-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_injective
-- name    : Formalism.HN.PlaceDecomposition.psi_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:47.445637+00:00
-- url     : https://prove2.me/theorems/3e4a35be-0f28-4e6a-93c7-6f1ea5062f9d
-- title:
--   Place Decomposition: psi injective
-- statement:
--   The Place Decomposition construction uses the psi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L138-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L138-L143

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

theorem Formalism.HN.PlaceDecomposition.psi_injective (v : P) : Function.Injective (psi (ι := ι) v) := by sorry
